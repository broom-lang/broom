structure Typechecker :> sig
    type env = (FlexFAst.Type.concr, FlexFAst.Term.expr, TypeError.t) TypecheckingEnv.t

    val elaborateProgram: env -> Cst.Term.begin
        -> ( FlexFAst.Term.program * env * TypeError.t list
           , FlexFAst.Term.program * env) Either.t
end = struct
    val op|> = Fn.|>
    datatype either = datatype Either.t
    structure Uv = TypeVars.Uv
    structure CTerm = Cst.Term
    datatype explicitness = datatype Cst.explicitness
    structure FAst = FlexFAst
    structure FTerm = FAst.Term
    structure FType = FAst.Type
    structure Id = FType.Id
    structure Concr = FType.Concr
    datatype kind = datatype Kind.t
    datatype effect = datatype FType.effect
    datatype sv = datatype FType.sv
    datatype concr = datatype FAst.Type.concr'
    type concr = FType.concr

    open TypeError

    structure Env = TypecheckingEnv
    structure Bindings = Env.Bindings
    structure Scope = Env.Scope
    type env = (FlexFAst.Type.concr, FlexFAst.Term.expr, TypeError.t) TypecheckingEnv.t
    datatype expr_binding_state = datatype Bindings.Expr.binding_state
    structure Path = TypeVars.Path

    val reAbstract = Kindchecker.reAbstract
    val applyCoercion = Subtyping.applyCoercion
    val subEffect = Subtyping.subEffect
    val subType = Subtyping.subType
    val unify = Subtyping.unify
    val joinEffs = Subtyping.joinEffs
    val rowWithout = TypecheckingOps.rowWithout

(* # Utils *)

    val rowWhere = TypecheckingOps.rowWhere (fn env => fn pos => fn base => fn label => fn (sub, super) =>
        ( subType env pos (sub, super)
        ; FType.RowExt {base, field = (label, sub)} )
    )

    val nameFromId = Name.fromString o Id.toString

    fun unvisitedBindingType env =
        #unvisitedBindingType (CheckUse.fix {elaborateType, reAbstract, instantiateExistential, elaborateExpr}) env
    and lookupValType pos =
        #lookupValType (CheckUse.fix {elaborateType, reAbstract, instantiateExistential, elaborateExpr}) pos

    and elaborateType env = (Kindchecker.fix {unvisitedBindingType, elaborateExpr}) env

(* # Expression Type Synthesis *)

    (* Elaborate the expression `exprRef` and return its computed type. *)
    and elaborateExpr (env: env) (expr: CTerm.expr): effect * concr * FTerm.expr =
        case expr
        of CTerm.Fn (pos, expl, clauses) => (* TODO: Exhaustiveness checking: *)
            (* FIXME: Enforce that for implicit fn:s domain = type *)
            let val codomain = SVar (UVar (Uv.fresh env TypeK))
                val (eff, domain, clauses) =
                    elaborateClauses env (fn (env, body) => elaborateExprAs env codomain body) clauses
                val (typeDefs, domain) =
                    case domain
                    of SOME (typeDefs, domain) => (typeDefs, domain)
                     | NONE => (#[], SVar (UVar (Uv.fresh env TypeK)))
                val def = {pos, id = DefId.fresh (), var = Name.fresh (), typ = domain}
                val arr =
                    case (expl, eff)
                    of (Implicit, Pure) => Implicit
                     | (Implicit, Impure) => raise Fail "Impure body on implicit function"
                     | (Explicit (), _) => Explicit eff
            in ( Pure
               , let val arrow = Arrow (arr, {domain, codomain})
                 in case Vector1.fromVector typeDefs
                    of SOME typeDefs => ForAll (typeDefs, arrow)
                     | NONE => arrow
                 end
               , let val f = FTerm.Fn ( pos, def, arr
                                      , FTerm.Match ( pos, codomain, FTerm.Use (pos, def)
                                                    , clauses ) )
                 in case Vector1.fromVector typeDefs
                    of SOME typeDefs => FTerm.TFn (pos, typeDefs, f)
                     | NONE => f
                 end )
            end
         | CTerm.Begin (pos, defns, body) =>
            let val scope = defsScope env defns
                val env = Env.pushScope env scope
                val stmts = elaborateDefs env defns
                val (eff, typ, body) = elaborateExpr env body
            in ( eff, typ
               , case Vector1.fromVector stmts
                 of SOME stmts => FTerm.Letrec (pos, stmts, body)
                  | NONE => body )
            end

         | CTerm.Do (pos, stmts, body) =>
            let val step =
                   fn (CTerm.Val (pos, pat, expr), (revStmts, eff, env)) =>
                       let val ((typeDefs, tbody), pattern as FTerm.Def (_, {pos, id, var, typ = _})) =
                               elaboratePattern env pat
                           val (exprEff, t, expr) = elaborateAsExists env (typeDefs, tbody) expr
                           val def = {pos, id, var, typ = t}
                       in ( FTerm.Val (pos, def, expr) :: revStmts
                          , joinEffs (eff, exprEff)
                          , Env.pushScope env (Scope.PatternScope ( Scope.Id.fresh (), var
                                                                  , Visited (def, SOME (exprEff, expr)) )) )
                       end
                    | (CTerm.Expr expr, (revStmts, eff, env)) =>
                       let val (exprEff, t, expr) = elaborateExpr env expr
                       in ( FTerm.Expr expr :: revStmts
                          , joinEffs (eff, exprEff)
                          , env )
                       end
                val (revStmts, stmtsEff, env) = Vector.foldl step ([], Pure, env) stmts
                val (bodyEff, typ, body) = elaborateExpr env body
            in ( joinEffs (stmtsEff, bodyEff), typ
               , case Vector1.fromList (List.rev revStmts)
                 of SOME stmts => FTerm.Let (pos, stmts, body)
                  | NONE => body )
            end

         | CTerm.Match (_, _, _) =>
            let val t = SVar (UVar (Uv.fresh env TypeK))
                val (eff, expr) = elaborateExprAs env t expr
            in (eff, t, expr)
            end
         (* TODO: Descend into subcomponents of records and modules so that e.g.
                  `module val id = fn _ => fn x => x end : interface val id: fun a: type => a -> a end`
                  will work. It would also avoid an intermediate record in the elaborated code. *)
         | CTerm.Record (pos, fields) => elaborateRecord env pos fields

         | CTerm.Module (pos, extension, stmts) =>
            let val (baseEff, FType.Record baseRow, baseStmt, baseUse, env) =
                    case extension
                    of SOME (pat, expr) =>
                        let val (def, var, eff, typ, expr) =
                                case pat
                                of SOME pat =>
                                    let val ((typeDefs, tbody), FTerm.Def (_, def as {var, ...})) =
                                            elaboratePattern env pat
                                        val (eff, typ, expr) = elaborateAsExists env (typeDefs, tbody) expr
                                    in (def, var, eff, typ, expr)
                                    end
                                 | NONE =>
                                    let val (eff, typ, expr) = elaborateExpr env expr
                                        val id = DefId.fresh ()
                                        val var = Name.fresh ()
                                    in ({pos, id, var, typ}, var, eff, typ, expr)
                                    end
                        in ( eff
                           , typ
                           , SOME (FTerm.Val (pos, def, expr))
                           , FTerm.Use (pos, def)
                           , Env.pushScope env (Scope.PatternScope ( Scope.Id.fresh (), var
                                                                   , Visited (def, SOME (eff, expr)) )) )
                        end
                      | NONE => (Pure, FType.Record FType.EmptyRow, NONE, FTerm.EmptyRecord pos , env)

                val env = Env.pushScope env (membersScope env stmts)
                val (row, revStmts, body) =
                    Vector.foldl (fn (Cst.Extend defn, (base, revStmts, body)) =>
                                      (case elaborateDefn env defn
                                       of (Pure, stmt as FTerm.Val (pos, def as {var, typ, ...}, _)) =>
                                           let val row = FType.RowExt {base, field = (var, typ)}
                                               val use = FTerm.Use (pos, def)
                                           in  ( row
                                               , stmt :: revStmts
                                               , FTerm.With (pos, Record row, {base = body, field = (var, use)}) )
                                           end)
                                   | (Cst.Override defn, (base, revStmts, body)) =>
                                      (case elaborateDefn env defn
                                       of (Pure, stmt as FTerm.Val (pos, def as {var, typ, ...}, _)) =>
                                           let val row = rowWhere env pos (base, (var, typ))
                                               val use = FTerm.Use (pos, def)
                                           in  ( row
                                               , stmt :: revStmts
                                               , FTerm.Where (pos, Record row, {base = body, field = (var, use)}) )
                                           end)
                                   | (Cst.Exclude (pos, label), (base, revStmts, body)) =>
                                      let val row = rowWithout env pos (base, label)
                                      in  ( row
                                          , revStmts
                                          , FTerm.Without (pos, Record row, {base = body, field = label}) )
                                      end)
                                 (baseRow, [], baseUse) stmts
                val stmts = Vector.fromList (List.rev revStmts)

                val expr =
                    case Vector1.fromVector stmts
                    of SOME stmts => FTerm.Letrec (pos, stmts, body)
                     | NONE => body
                val expr =
                    case baseStmt
                    of SOME baseStmt => FTerm.Let (pos, Vector1.singleton baseStmt, expr)
                     | NONE => expr
            in (baseEff, Record row, expr)
            end

         | CTerm.App (pos, {callee, arg}) =>
            (* FIXME: generative behaviour when `callEff` is `Impure`: *)
            let val (calleeEff, calleeTyp, callee) = elaborateExpr env callee
                val (callee, callEff, {domain, codomain}) = coerceCallee env (calleeTyp, callee)
                val (argEff, arg) = elaborateExprAs env domain arg
            in ( joinEffs (joinEffs (calleeEff,  argEff), callEff), codomain
               , FTerm.App (pos, codomain, {callee, arg}) )
            end
         | CTerm.PrimApp (pos, opn, args) =>
            let val (tparams, appEff, {domain, codomain}) = FType.primopType opn
                val namedTargs = Vector.map (fn {var, kind} => (var, SVar (UVar (Uv.fresh env kind))))
                                            tparams
                val targs = Vector.map #2 namedTargs
                val mapping = Id.SortedMap.fromVector namedTargs
                val domain = Vector.map (Concr.substitute env mapping) domain
                val codomain = Concr.substitute env mapping codomain

                do if not (Vector.length domain = Vector.length args)
                   then raise Fail "argc"
                   else ()
                val (eff, revArgs) =
                    Vector.foldl (fn ((t, arg), (eff, revArgs)) =>
                                      let val (argEff, arg) = elaborateExprAs env t arg
                                      in (joinEffs (eff, argEff), arg :: revArgs)
                                      end)
                                 (appEff, [])
                                 (VectorExt.zip (domain, args))
            in (eff, codomain, FTerm.PrimApp (pos, codomain, opn, targs, Vector.fromList (List.rev revArgs)))
            end
         | CTerm.Field (pos, expr, label) =>
            let val (eff, t, expr) = elaborateExpr env expr
                val (expr, fieldType) = coerceRecord env (t, expr) label
            in (eff, fieldType, FTerm.Field (pos, fieldType, expr, label))
            end
         | CTerm.Ann (_, expr, t) =>
            let val (defs, t) = elaborateType env t
            in elaborateAsExists env (Vector.fromList defs, t) expr
            end
         | CTerm.Type (pos, t) =>
            let val (defs, body) = elaborateType env t
                val t =
                    case Vector1.fromList defs
                    of SOME defs => Exists (defs, body)
                     | NONE => body
            in (Pure, Type t, FTerm.Type (pos, t))
            end
         | CTerm.Use (pos, name) =>
            let val def = case lookupValType expr name env
                          of SOME def => def
                           | NONE => ( Env.error env (UnboundVal (pos, name))
                                     ; { pos, id = DefId.fresh (), var = name
                                       , typ = SVar (UVar (Uv.fresh env TypeK)) } )
            in (Pure, #typ def, FTerm.Use (pos, def))
            end
         | CTerm.Const (pos, c) =>
            (Pure, Prim (Const.typeOf c), FTerm.Const (pos, c))

    (* Should we start elaboration from more annotated patterns, to enable e.g.
       `{| x -> ... | a: type -> ...}` ? *)
    and elaborateClauses env elaborateBody clauses =
        let fun elaborateClause ({pattern, body}, (matcheeTyp, eff, clauses)) =
                let val (matcheeTyp, pattern, env) =
                        case matcheeTyp
                        of SOME (typeDefs, matcheeTyp') =>
                            let val env =
                                    case Vector1.fromVector typeDefs
                                    of SOME typeDefs =>
                                        Env.pushScope env (Scope.ForAllScope ( Scope.Id.fresh ()
                                                                             , Bindings.Type.fromDefs typeDefs ))
                                     | NONE => env
                                val (pattern, env) = elaboratePatternAs env matcheeTyp' pattern
                            in (matcheeTyp, pattern, env)
                            end
                         | NONE =>
                            let val (matcheeTyp as (typeDefs, _), pattern) = elaboratePattern env pattern
                                val env =
                                    case Vector1.fromVector typeDefs
                                    of SOME typeDefs =>
                                        Env.pushScope env (Scope.ForAllScope (Scope.Id.fresh (), Bindings.Type.fromDefs typeDefs))
                                     | NONE => env
                                val env =
                                    case pattern
                                    of FTerm.Def (_, def as {var, ...}) =>
                                        Env.pushScope env (Scope.PatternScope (Scope.Id.fresh (), var, Visited (def, NONE)))
                                     | FTerm.AnyP _ => env
                                     | FTerm.ConstP _ => env
                            in (SOME matcheeTyp, pattern, env)
                            end
                    val (bodyEff, body) = elaborateBody (env, body)
                in (matcheeTyp, joinEffs (eff, bodyEff), {pattern, body} :: clauses)
                end
            val (matcheeTyp, eff, clauses) = Vector.foldl elaborateClause (NONE, Pure, []) clauses
        in (eff, matcheeTyp, Vector.fromList (List.rev clauses))
        end

    and elaboratePattern env =
        fn CTerm.AnnP (pos, {pat, typ}) =>
            let val (typeDefs, t) = elaborateType env typ
                val (pat, _) = elaboratePatternAs env t pat
            in ((Vector.fromList typeDefs, t), pat)
            end
         | CTerm.Def (pos, name) =>
            let val t = SVar (UVar (Uv.fresh env TypeK))
                val def = {pos, id = DefId.fresh (), var = name, typ = t}
            in ((#[], t), FTerm.Def (pos, def))
            end
         | CTerm.AnyP pos => ((#[], SVar (UVar (Uv.fresh env TypeK))), FTerm.AnyP pos)
         | CTerm.ConstP (pos, c) =>
            let val cTyp = Prim (Const.typeOf c)
            in ((#[], cTyp), FTerm.ConstP (pos, c))
            end

    and elaborateRecord env pos ({base, edits}: CTerm.recordFields): effect * concr * FTerm.expr =
        let fun elaborateEdit (edit, acc) =
                case edit
                of CTerm.With fields =>
                    Vector.foldl (fn ((label, expr), (eff, base, baseExpr)) =>
                                      let val (fieldEff, fieldTyp, fieldExpr) = elaborateExpr env expr
                                          val row = RowExt {base, field = (label, fieldTyp)}
                                      in ( joinEffs (eff, fieldEff)
                                         , row
                                         , FTerm.With (pos, Record row, {base = baseExpr, field = (label, fieldExpr)}) )
                                      end)
                                 acc fields
                 | CTerm.Where fields =>
                    Vector.foldl (fn ((label, expr), (eff, base, baseExpr)) =>
                                      let val (fieldEff, fieldTyp, fieldExpr) = elaborateExpr env expr
                                          val row = rowWhere env pos (base, (label, fieldTyp))
                                      in ( joinEffs (eff, fieldEff)
                                         , row
                                         , FTerm.Where (pos, Record row, {base = baseExpr, field = (label, fieldExpr)}) )
                                      end)
                                 acc fields
                 | CTerm.Without labels =>
                    Vector.foldl (fn (label, (eff, base, baseExpr)) =>
                                      let val row = rowWithout env pos (base, label)
                                      in (eff, row, FTerm.Without (pos, Record row, {base = baseExpr, field = label}))
                                      end)
                                 acc labels

            val (baseEff, baseType, baseExpr) =
                case base
                of SOME base =>
                    let val (baseEff, t, base) = elaborateExpr env base
                    in case t
                       of Record row => (baseEff, row, base)
                    end
                 | NONE => (Pure, EmptyRow, FTerm.EmptyRecord pos)
            val (eff, rowType, expr) =
                Vector.foldl elaborateEdit (baseEff, baseType, baseExpr) edits
        in (eff, Record rowType, expr)
        end

(* # Expression Type Checking *)

    (* Elaborate the expression `exprRef` to a subtype of `typ`. *)
    and elaborateExprAs (env: env) (typ: concr) (expr: CTerm.expr): effect * FTerm.expr =
        case expr
        of CTerm.Fn (pos, expl, clauses) => (* TODO: Exhaustiveness checking: *)
            (case typ
             of ForAll args => elaborateAsForAll env args expr
              | Arrow (expl', {domain, codomain}) =>
                 ( case (expl, expl')
                   of ((Implicit, Implicit) | (Explicit (), Explicit _)) => ()
                    | _ => raise Fail "Explicitness mismatch" 
                 ; let val (eff, clauses) =
                           elaborateClausesAs env domain
                               (fn (env, body) => elaborateExprAs env codomain body)
                               clauses
                       val def = {pos, id = DefId.fresh (), var = Name.fresh (), typ = domain}
                       val arr =
                           case (expl', eff)
                           of (Implicit, Pure) => Implicit
                            | (Implicit, Impure) => raise Fail "Impure body on implicit function"
                            | (Explicit eff', _) => (subEffect pos (eff, eff'); expl')
                   in ( Pure
                      , FTerm.Fn ( pos, def, arr
                                 , FTerm.Match ( pos, codomain, FTerm.Use (pos, def)
                                               , clauses ) ) )
                   end )
              | _ => coerceExprTo env typ expr)
         | CTerm.Match (pos, matchee, clauses) => (* TODO: Exhaustiveness checking: *)
            let val (matcheeEff, matcheeTyp, matchee) = elaborateExpr env matchee
                val (clausesEff, clauses) =
                    elaborateClausesAs env matcheeTyp
                        (fn (env, body) => elaborateExprAs env typ body)
                        clauses
            in (joinEffs (matcheeEff, clausesEff), FTerm.Match (pos, typ, matchee, clauses))
            end
         | _ =>
            (case typ
             of ForAll args => elaborateAsForAll env args expr
              | _ => coerceExprTo env typ expr)

    and elaborateAsForAll env (params, body) expr =
        let val scopeId = Scope.Id.fresh ()
            val env = Env.pushScope env (Scope.ForAllScope (scopeId, Bindings.Type.fromDefs params))
            val (eff, expr) = elaborateExprAs env body expr
        in (eff, FTerm.TFn (FTerm.exprPos expr, params, expr))
        end

    and elaborateClausesAs env matcheeTyp elaborateBody clauses =
        let val (eff, revClauses) =
                Vector.foldl (fn (clause, (eff, clauses)) =>
                                  let val (clauseEff, clause) = elaborateClauseAs env matcheeTyp elaborateBody clause
                                  in (joinEffs (eff, clauseEff), clause :: clauses)
                                  end)
                             (Pure, []) clauses
        in (eff, Vector.fromList (List.rev revClauses))
        end

    and elaborateClauseAs env matcheeTyp elaborateBody {pattern, body} =
        let val (pattern, env) = elaboratePatternAs env matcheeTyp pattern
            val (eff, body) = elaborateBody (env, body)
        in (eff, {pattern, body})
        end

    and elaboratePatternAs env t =
        fn CTerm.AnnP (_, {pat, typ}) => raise Fail "unimplemented"
         | CTerm.Def (pos, name) =>
            let val def = {pos, id = DefId.fresh (), var = name, typ = t}
            in ( FTerm.Def (pos, def)
               , Env.pushScope env (Scope.PatternScope (Scope.Id.fresh (), name, Visited (def, NONE))) )
            end
         | CTerm.AnyP pos => (FTerm.AnyP pos, env)
         | CTerm.ConstP (pos, c) =>
            let val cTyp = Prim (Const.typeOf c)
                val _ = unify env pos (cTyp, t)
            in (FTerm.ConstP (pos, c), env)
            end

    and elaborateAsExists env t expr: effect * concr * FTerm.expr =
        let val tWithCtx as (t, _) = instantiateExistential env t
            val (eff, expr) = elaborateAsExistsInst env tWithCtx expr
        in (eff, t, expr)
        end

    and instantiateExistential env (params: FType.def vector, body): concr * concr vector = 
        let val paths = Vector.map (fn {var = _, kind} =>
                                        let val face = CallTFn (Env.freshAbstract env kind)
                                        in FAst.Type.SVar (Path (Path.new (kind, face)))
                                        end)
                                   params
           
            val mapping = (params, paths)
                        |> VectorExt.zipWith (fn ({var, ...}, path) => (var, path))
                        |> Id.SortedMap.fromVector
            val implType = Concr.substitute env mapping body
        in (implType, paths)
        end

    and elaborateAsExistsInst env (implType, paths) =
        fn CTerm.Match (pos, matchee, clauses) =>
            let val (matcheeEff, matcheeTyp, matchee) = elaborateExpr env matchee
                val (clausesEff, clauses) =
                    elaborateClausesAs env matcheeTyp
                                       (fn (env, body) => elaborateAsExistsInst env (implType, paths) body)
                                       clauses
                val eff = joinEffs (matcheeEff, clausesEff)
                val eff = if Vector.length paths = 0
                          then eff
                          else Impure
            in (eff, FTerm.Match (pos, implType, matchee, clauses))
            end
         | expr =>
            let val scopeId = Scope.Id.fresh ()
                val env = Env.pushScope env (Scope.Marker scopeId)
                val pos = CTerm.exprPos expr
                val coercionNames = Vector.map (fn FAst.Type.SVar (Path path) =>
                                                    let val name = Name.freshen (Name.fromString "coImpl")
                                                        do Path.addScope env path (scopeId, name)
                                                    in name
                                                    end)
                                               paths
                val (eff, expr) = elaborateExprAs env implType expr
                val axiomStmts =
                    VectorExt.zipWith (fn (FAst.Type.SVar (Path path), name) =>
                                        let val face = Path.face path
                                            val params =
                                                let fun kindParams params =
                                                        fn ArrowK {domain, codomain} =>
                                                            kindParams ({var = FType.Id.fresh (), kind = domain} :: params)
                                                                       codomain
                                                         | _ => Vector.fromList (List.rev params)
                                                in kindParams [] (Path.kind path)
                                                end
                                            val (impl, _) = Either.unwrap (Path.get env path)
                                        in  case Vector1.fromVector params
                                            of SOME params =>
                                                let val args = Vector1.map (fn def => UseT def) params
                                                in FTerm.Axiom ( pos, name
                                                               , ForAll (params, App {callee = face, args})
                                                               , ForAll (params, SVar (UVar impl)) )
                                                end
                                             | NONE => FTerm.Axiom (pos, name, face, SVar (UVar impl))
                                        end)    
                                   (paths, coercionNames)
            in ( eff
               , case Vector1.fromVector axiomStmts
                 of SOME axiomStmts => FTerm.Letrec (pos, axiomStmts, expr)
                  | NONE => expr )
            end

    (* Like `elaborateExprAs`, but will always just do subtyping and apply the coercion. *)
    and coerceExprTo (env: env) (typ: concr) (expr: CTerm.expr): effect * FTerm.expr =
        let val (eff, t', fexpr) = elaborateExpr env expr
            val coercion = subType env (CTerm.exprPos expr) (t', typ)
        in (eff, applyCoercion coercion fexpr)
        end

(* # Statement Type Checking *)

    and elaborateDefs env stmts =
        let val revStmts =
                Vector.foldl (fn (stmt, stmts') =>
                                  (* TODO: Allow 'dyn' effect (from sealing `Match`) when it arrives: *)
                                  case elaborateDefn env stmt
                                  of (Pure, stmt) => stmt :: stmts'
                                   | (Impure, _) => raise Fail "Impure stmt in pure context.")
                             [] stmts
        in Vector.fromList (List.rev revStmts)
        end

    and defsScope env defns =
        let val builder = Bindings.Expr.Builder.new ()
            do Vector.app (fn (_, CTerm.Def (pos, name), expr) =>
                               let val def = {pos, id = DefId.fresh (), var = name, typ = NONE}
                               in case Bindings.Expr.Builder.insert builder pos name (Unvisited (def, SOME expr))
                                  of Left err => Env.error env (DuplicateBinding err)
                                   | Right res => res
                               end
                            | (_, CTerm.AnnP (_, {pat = CTerm.Def (pos, name), typ}), expr) =>
                               let val def = {pos, id = DefId.fresh (), var = name, typ = SOME typ}
                               in case Bindings.Expr.Builder.insert builder pos name (Unvisited (def, SOME expr))
                                  of Left err => Env.error env (DuplicateBinding err)
                                   | Right res => res
                               end)
                          defns
        in Scope.BlockScope (Scope.Id.fresh (), Bindings.Expr.Builder.build builder)
        end

    and stmtsScope env stmts =
        let val builder = Bindings.Expr.Builder.new ()
            do Vector.app (fn CTerm.Val (_, CTerm.Def (pos, name), expr) =>
                               let val def = {pos, id = DefId.fresh (), var = name, typ = NONE}
                               in case Bindings.Expr.Builder.insert builder pos name (Unvisited (def, SOME expr))
                                  of Left err => Env.error env (DuplicateBinding err)
                                   | Right res => res
                               end
                            | CTerm.Val (_, CTerm.AnnP (_, {pat = CTerm.Def (pos, name), typ}), expr) =>
                               let val def = {pos, id = DefId.fresh (), var = name, typ = SOME typ}
                               in case Bindings.Expr.Builder.insert builder pos name (Unvisited (def, SOME expr))
                                  of Left err => Env.error env (DuplicateBinding err)
                                   | Right res => res
                               end
                            | CTerm.Expr _ => ())
                          stmts
        in Scope.BlockScope (Scope.Id.fresh (), Bindings.Expr.Builder.build builder)
        end

    and membersScope env members =
        let val builder = Bindings.Expr.Builder.new ()
            do Vector.app (fn (Cst.Extend (_, CTerm.Def (pos, name), expr) | Cst.Override (_, CTerm.Def (pos, name), expr)) =>
                               let val def = {pos, id = DefId.fresh (), var = name, typ = NONE}
                               in case Bindings.Expr.Builder.insert builder pos name (Unvisited (def, SOME expr))
                                  of Left err => Env.error env (DuplicateBinding err)
                                   | Right res => res
                               end
                            | ( Cst.Extend (_, CTerm.AnnP (_, {pat = CTerm.Def (pos, name), typ}), expr)
                              | (Cst.Override (_, CTerm.AnnP (_, {pat = CTerm.Def (pos, name), typ}), expr)) ) =>
                               let val def = {pos, id = DefId.fresh (), var = name, typ = SOME typ}
                               in case Bindings.Expr.Builder.insert builder pos name (Unvisited (def, SOME expr))
                                  of Left err => Env.error env (DuplicateBinding err)
                                   | Right res => res
                               end
                            | Cst.Exclude _ => ())
                          members
        in Scope.BlockScope (Scope.Id.fresh (), Bindings.Expr.Builder.build builder)
        end

    and elaborateMember env =
        fn (Cst.Extend defn | Cst.Override defn) => SOME (elaborateDefn env defn)
         | Cst.Exclude _ => NONE

    (* Elaborate a statement and return the elaborated version. *)
    and elaborateStmt env: Cst.Term.stmt -> effect * FTerm.stmt =
        fn CTerm.Val defn => elaborateDefn env defn
         | CTerm.Expr expr =>
            let val (eff, expr) = elaborateExprAs env (FType.Record FType.EmptyRow) expr
            in (eff, FTerm.Expr expr)
            end

    and elaborateDefn env (pos, pat, expr) =
        let val rec patName =
                fn CTerm.Def (_, name) => name
                 | CTerm.AnnP (_, {pat, ...}) => patName pat
            val name = patName pat
            val def as {typ = t, ...} = valOf (lookupValType expr name env) (* `name` is in `env` by construction *)
            val (eff, expr) =
                case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                of (Unvisited _ | Visiting _) => raise Fail "unreachable" (* Not possible after `lookupValType`. *)
                 | Typed ({typ = (_, ctx), ...}, SOME expr) =>
                    (case ctx
                     of SOME namedPaths => elaborateAsExistsInst env (t, namedPaths) expr
                      | NONE => elaborateExprAs env t expr)
                 | Visited (_, SOME effxpr) => effxpr
                 | (Typed (_, NONE) | Visited (_, NONE)) => raise Fail "unreachable"
        in (eff, FTerm.Val (pos, def, expr))
        end

(* # Focalization *)

    and coerceCallee env (typ, callee) =
        case TypePattern.coerce env TypePattern.callable (callee, typ)
        of (callee, TypePattern.Callable (eff, domains)) => (callee, eff, domains)
         | _ => raise Fail "unreachable"
   
    and coerceRecord env (typ, expr) label =
        case TypePattern.coerce env (TypePattern.hasField label) (expr, typ)
        of (expr, TypePattern.HasField (_, fieldt)) => (expr, fieldt)
         | _ => raise Fail "unreachable"
    
(* Type Checking Entire Program *)

    (* TODO: Prevent boundless deepening of REPL env
             and enable forward decl:s for stmts to be input on later lines. *)
    fun elaborateProgram env (codePos, defns, body) =
        let val scope = defsScope env defns
            val env = Env.pushScope env scope
            val stmts = elaborateDefs env defns
            val (eff, body) = elaborateExprAs env (FType.Prim PrimType.Int) body
            val program = { typeFns = Env.typeFns env
                            (* `valOf` is fine since the empty program also lacks `main`: *)
                          , code = (codePos, valOf (Vector1.fromVector stmts), body)
                          , sourcemap = Env.sourcemap env }
        in case Env.errors env
           of [] => Right (program, env)
            | errors => Left (program, env, errors)
        end
end

