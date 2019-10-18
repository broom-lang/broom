structure Typechecker :> sig
    val elaborateProgram: TypecheckingEnv.t -> Cst.Term.stmt vector
        -> ( FlexFAst.Term.program * TypecheckingEnv.t * TypeError.t list
           , FlexFAst.Term.program * TypecheckingEnv.t ) Either.t
end = struct
    val op|> = Fn.|>
    datatype either = datatype Either.t
    structure Uv = TypeVars.Uv
    datatype predicativity = datatype TypeVars.predicativity
    structure CTerm = Cst.Term
    structure CType = Cst.Type
    datatype explicitness = datatype Cst.explicitness
    structure FAst = FlexFAst
    structure FTerm = FAst.Term
    structure FType = FAst.Type
    structure Id = FType.Id
    structure Concr = FType.Concr
    datatype effect = datatype FType.effect
    datatype abs' = datatype FAst.Type.abs'
    type concr = FType.concr
    val concr = FType.Abs.concr

    open TypeError

    structure Env = TypecheckingEnv
    structure Bindings = Env.Bindings
    structure Scope = Env.Scope
    datatype expr_binding_state = datatype Bindings.Expr.binding_state
    structure Path = TypeVars.Path
 
    val applyCoercion = Subtyping.applyCoercion
    val subEffect = Subtyping.subEffect
    val subType = Subtyping.subType
    val unify = Subtyping.unify

    fun uvSet env =
        Uv.set Concr.tryToUv Scope.Id.compare (Env.hasScope env)

    val nameFromId = Name.fromString o Id.toString

(* Looking up statement/declaration types *)

    fun unvisitedBindingType pos env name args : FTerm.def =
        let do Env.updateExpr pos env name (Fn.constantly (Visiting args)) (* Mark binding 'grey'. *)
            val (def, binding') =
                case args
                of (def as {typ = SOME t, ...}, oexpr) =>
                    (case elaborateType env t
                     of ([], t) =>
                         (FTerm.setDefTyp def t, Typed (FTerm.setDefTyp def (t, NONE), oexpr))
                      | (defs, t) =>
                         (case valOf (Env.innermostScope env)
                          of Scope.InterfaceScope _ =>
                              let val abst = Exists (Vector.fromList defs, t)
                                  val t = reAbstract env abst (* OPTIMIZE *)
                              in (FTerm.setDefTyp def t, Typed (FTerm.setDefTyp def (t, NONE), oexpr))
                              end
                           | _ =>
                              let val (t, paths) =
                                      instantiateExistential env (Exists (Vector.fromList defs, t))
                              in (FTerm.setDefTyp def t, Typed (FTerm.setDefTyp def (t, SOME paths), oexpr))
                              end))
                 | (def as {typ = NONE, ...}, SOME expr) =>
                    let val (eff, t, expr) = elaborateExpr env expr (* FIXME: use `eff` *)
                        val def = FTerm.setDefTyp def t
                    in (def, Visited (def, SOME (eff, expr)))
                    end
                 | (def as {typ = NONE, ...}, oexpr as NONE) =>
                    let val t = FType.SVar (FType.UVar (Env.freshUv env Predicative))
                    in (FTerm.setDefTyp def t, Typed (FTerm.setDefTyp def (t, NONE), oexpr))
                    end
        in case valOf (Env.findExpr env name)
           of Unvisited _ => raise Fail "unreachable" (* State is at 'least' `Visiting`. *)
            | Visiting _ =>
               ( Env.updateExpr pos env name (Fn.constantly binding')
               ; def )
            | Typed ({typ = (usageTyp, NONE), ...}, _) | Visited ({typ = usageTyp, ...}, _) =>
               (* We must have found a cycle and used `cyclicBindingType`. *)
               ( ignore (subType env pos (#typ def, usageTyp))
               ; FTerm.setDefTyp def usageTyp )
            | Typed ({typ = (_, SOME _), ...}, _) => raise Fail "unreachable"
        end
      
    (* In case we encounter a recursive reference to `name` not broken by type annotations we call
       this to insert a unification variable, inferring a monomorphic type. *)
    and cyclicBindingType pos env name (def, oexpr) : FTerm.def =
        let val t = FType.SVar (FType.UVar (Env.freshUv env Predicative))
        in Env.updateExpr pos env name (Fn.constantly (Typed ( FTerm.setDefTyp def (t, NONE)
                                                             , oexpr )))
         ; FTerm.setDefTyp def t
        end

    (* Get the type of the variable `name`, referenced at `pos`, from `env` by either
       - finding the type annotation (if available) (and elaborating it if not already done)
       - elaborating the expression bound to the variable (if available)
       - returning a fresh unification variable (if neither type annotation nor bound expression
         is available or if a cycle is encountered) *)
    and lookupValType expr name env : FTerm.def option =
        Option.map (fn (Unvisited args, env) => unvisitedBindingType (CTerm.exprPos expr) env name args
                     | (Visiting args, env) =>
                        let val pos = CTerm.exprPos expr
                        in case valOf (Env.innermostScope env)
                           of Scope.InterfaceScope _ => raise Fail ("Type cycle at " ^ Pos.toString pos)
                            | _ => cyclicBindingType pos env name args
                        end
                     | (Typed (def, _), _) => FTerm.updateDefTyp def #1
                     | (Visited (def, _), _) => def)
                   (Env.findExprClosure env name)

    and reAbstract env =
        fn Exists (params, body) =>
            let val (_, absBindings) = valOf (Env.nearestExists env)
                val mapping =
                    Vector.foldl (fn ({var, kind}, mapping) =>
                                      let val args = Env.universalParams env
                                          val kind = Vector.foldr (fn ({var = _, kind = argKind}, kind) =>
                                                                       FType.ArrowK { domain = argKind
                                                                                    , codomain = kind })
                                                                  kind args
                                          val var' = Bindings.Type.fresh absBindings kind
                                          val app = FType.app { callee = FType.UseT {var = var', kind}
                                                              , args = Vector.map (fn def => FType.UseT def)
                                                                                  args }
                                      in Id.SortedMap.insert (mapping, var, app)
                                      end)
                                 Id.SortedMap.empty params
            in Concr.substitute (Env.hasScope env) mapping body
            end

(* Elaborating subtrees *)

    (* Elaborate the type `typ` and return the elaborated version. *)
    and elaborateType (env: Env.t) (t: CType.typ): FType.def list * concr =
        let val absBindings = Bindings.Type.new ()
            val absScope = Scope.ExistsScope (Scope.Id.fresh (), absBindings)
            val env = Env.pushScope env absScope

            fun elaborate env =
                fn CType.Pi (pos, {var, typ = domain}, expl, codomain) =>
                    let val (nonCallsiteTypeDefs, domain) =
                            case domain
                            of SOME domain => elaborateType env domain
                             | NONE => ([], FType.SVar (FType.UVar (Env.freshUv env Predicative)))
                        val callsite = {var = FType.Id.fresh (), kind = FType.CallsiteK}
                        val typeDefs = callsite :: nonCallsiteTypeDefs

                        val env = Env.pushScope env (Scope.ForAllScope ( Scope.Id.fresh ()
                                                                       , typeDefs
                                                                         |> Vector.fromList
                                                                         |> Bindings.Type.fromDefs ))
                        val def = {pos = pos, id = DefId.fresh (), var, typ = domain}
                        val fnScope = Scope.FnScope (Scope.Id.fresh (), var, Visited (def, NONE))
                        val env = Env.pushScope env fnScope

                        val codomain = elaborate env codomain
                        val arrow = FType.Arrow (elaborateArr expl, {domain, codomain})
                        (* TODO: No callsite when `Implicit`: *) 
                        val typeDefs = if List.null nonCallsiteTypeDefs andalso FType.Concr.isSmall codomain
                                       then nonCallsiteTypeDefs
                                       else typeDefs
                    in case typeDefs
                       of [] => arrow
                        | _ => FType.ForAll (Vector.fromList typeDefs, arrow)
                    end
                 | CType.RecordT (pos, row) => FType.Record (elaborate env row)
                 | CType.RowExt (pos, {fields, ext}) =>
                    let fun step ((label, t), ext) =
                            FType.RowExt {field = (label, elaborate env t), ext}
                    in Vector.foldr step (elaborate env ext) fields
                    end
                 | CType.EmptyRow _ => FType.EmptyRow
                 | CType.WildRow _ =>
                    let val kind = FType.RowK
                        val var = Bindings.Type.fresh absBindings kind
                    in FType.UseT {var, kind}
                    end
                 | CType.Interface (pos, decls) =>
                    let val env = Env.pushScope env (declsScope decls)
                        val fields = Vector.map (elaborateDecl env) decls
                        fun constructStep (field, ext) = FType.RowExt {field, ext}
                    in FType.Record (Vector.foldr constructStep FType.EmptyRow fields)
                    end
                 | CType.Path pathExpr =>
                    let val (eff, t, _) = elaborateExpr env pathExpr
                    in case eff
                       of Pure =>
                           (case t
                            of FType.Type t => reAbstract env t
                             | _ => raise Fail ("Type path " ^ CTerm.exprToString pathExpr
                                            ^ "does not denote type at " ^ Pos.toString (CTerm.exprPos pathExpr)))
                        | _ => raise Fail "Impure type path expression"
                    end
                 | CType.TypeT pos =>
                    let val args = Env.universalParams env
                        val kind = Vector.foldr (fn ({var = _, kind = argKind}, kind) =>
                                                     FType.ArrowK {domain = argKind, codomain = kind})
                                                FType.TypeK args
                        val var = Bindings.Type.fresh absBindings kind
                        val app = FType.app { callee = FType.UseT {var, kind}
                                            , args = Vector.map (fn def => FType.UseT def)
                                                                args }
                    in FType.Type (concr app)
                    end
                 | CType.Singleton (_, expr) =>
                    (case elaborateExpr env expr
                     of (Pure, t, _) => t
                      | _ => raise Fail "Impure singleton type expression")
                 | CType.Prim (pos, p) => FType.Prim p

            and elaborateDecl env (_, name, _) =
                ( name
                , case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                  of Unvisited args => #typ (unvisitedBindingType (CType.pos t) env name args)
                   | Visiting _ => raise Fail ("Type cycle at " ^ Pos.toString (CType.pos t))
                   | Typed ({typ = (typ, _), ...}, _) | Visited ({typ, ...}, _) => typ )

            val t = elaborate env t
            val defs = Bindings.Type.defs absBindings
        in (defs, t)
        end

    and elaborateArr arr =
        case arr
        of Implicit => Implicit
         | Explicit eff => Explicit (elaborateEff eff)

    and elaborateEff eff =
        case eff
        of Cst.Pure => Pure
         | Cst.Impure => Impure

    and joinEffs effs =
        case effs
        of (Pure, Pure) => Pure
         | (Pure, Impure) => Impure
         | (Impure, Pure) => Impure
         | (Impure, Impure) => Impure

    and declsScope decls =
        let val builder = Bindings.Expr.Builder.new ()
            do Vector.app (fn (pos, var, t) =>
                               let val def = {pos, id = DefId.fresh (), var, typ = SOME t}
                               in Bindings.Expr.Builder.insert builder var (Unvisited (def, NONE))
                               end)
                          decls
        in Scope.InterfaceScope (Scope.Id.fresh (), Bindings.Expr.Builder.build builder)
        end

    and stmtsScope stmts =
        let val builder = Bindings.Expr.Builder.new ()
            do Vector.app (fn CTerm.Val (_, CTerm.Def (pos, name), expr) =>
                               let val def = {pos, id = DefId.fresh (), var = name, typ = NONE}
                               in Bindings.Expr.Builder.insert builder name (Unvisited (def, SOME expr))
                               end
                            | CTerm.Val (_, CTerm.AnnP (_, {pat = CTerm.Def (pos, name), typ}), expr) =>
                               let val def = {pos, id = DefId.fresh (), var = name, typ = SOME typ}
                               in Bindings.Expr.Builder.insert builder name (Unvisited (def, SOME expr))
                               end
                            | CTerm.Expr _ => ())
                          stmts
        in Scope.BlockScope (Scope.Id.fresh (), Bindings.Expr.Builder.build builder)
        end

    (* Elaborate the expression `exprRef` and return its computed type. *)
    and elaborateExpr (env: Env.t) (expr: CTerm.expr): effect * concr * FTerm.expr =
        case expr
        of CTerm.Fn (pos, expl, clauses) => (* TODO: Exhaustiveness checking: *)
            (* FIXME: Enforce that for implicit fn:s domain = type *)
            let val codomain = FType.SVar (FType.UVar (Env.freshUv env Predicative))
                val (eff, forallScopeId, domain, clauses) =
                    elaborateClauses env (fn (env, body) => elaborateExprAs env codomain body) clauses
                val (typeDefs, domain) =
                    case domain
                    of SOME (typeDefs, domain) => (typeDefs, domain)
                     | NONE => (#[], FType.SVar (FType.UVar (Env.freshUv env Predicative)))
                val def = {pos, id = DefId.fresh (), var = Name.fresh (), typ = domain}
                val arr =
                    case (expl, eff)
                    of (Implicit, Pure) => Implicit
                     | (Implicit, Impure) => raise Fail "Impure body on implicit function"
                     | (Explicit (), _) => Explicit eff
            in ( Pure
               , let val arrow = FType.Arrow (arr, {domain, codomain})
                 in case typeDefs
                    of #[] => arrow
                     | _ => FType.ForAll (typeDefs, arrow)
                 end
               , let val f = FTerm.Fn ( pos, Scope.Id.fresh (), def, arr
                                      , FTerm.Match ( pos, codomain, FTerm.Use (pos, def)
                                                    , clauses ) )
                 in case typeDefs
                    of #[] => f
                     | _ => FTerm.TFn (pos, forallScopeId, typeDefs, f)
                 end )
            end
         | CTerm.Let (pos, stmts, body) =>
            let val scope = stmtsScope stmts
                val env = Env.pushScope env scope
                val (stmtsEff, stmts) = elaborateStmts env stmts
                val (bodyEff, typ, body) = elaborateExpr env body
            in ( joinEffs (stmtsEff, bodyEff), typ
               , FTerm.Let (pos, Scope.id scope, stmts, body))
            end
         | CTerm.Match (pos, _, _) =>
            let val t = FType.SVar (FType.UVar (Env.freshUv env Predicative))
                val (eff, expr) = elaborateExprAs env t expr
            in (eff, t, expr)
            end
         (* TODO: Descend into subcomponents of records and modules so that e.g.
                  `module val id = fn _ => fn x => x end : interface val id: fun a: type => a -> a end`
                  will work. It would also avoid an intermediate record in the elaborated code. *)
         | CTerm.Record (pos, fields) => elaborateRecord env pos fields
         | CTerm.Module (pos, stmts) =>
            let val scope = stmtsScope stmts
                val env = Env.pushScope env scope
                val (eff, stmts) = elaborateStmts env stmts
                val defs = Vector.foldr (fn (FTerm.Val (_, def, _), defs) => def :: defs
                                          | (FTerm.Axiom _, defs) | (FTerm.Expr _, defs) => defs)
                                        [] stmts
                val row = List.foldl (fn ({var, typ, ...}, ext) => FType.RowExt {field = (var, typ), ext})
                                     FType.EmptyRow defs
                val typ = FType.Record row
                val body = FTerm.Extend ( pos, typ
                                        , Vector.fromList defs
                                              |> Vector.map (fn def as {var, ...} => (var, FTerm.Use (pos, def)))
                                        , NONE )
            in (eff, typ, FTerm.Let (pos, Scope.id scope, stmts, body))
            end
         | CTerm.App (pos, {callee, arg}) =>
            (* FIXME: generative behaviour when `callEff` is `Impure`: *)
            let val (calleeEff, calleeTyp, callee) = elaborateExpr env callee
                val (callee, callEff, {domain, codomain}) = coerceCallee env (calleeTyp, callee)
                val (argEff, arg) = elaborateExprAs env domain arg
            in ( joinEffs (joinEffs (calleeEff,  argEff), callEff), codomain
               , FTerm.App (pos, codomain, {callee, arg}) )
            end
         | CTerm.Field (pos, expr, label) =>
            let val (eff, t, expr) = elaborateExpr env expr
                val (expr, fieldType) = coerceRecord env (t, expr) label
            in (eff, fieldType, FTerm.Field (pos, fieldType, expr, label))
            end
         | CTerm.Ann (pos, expr, t) =>
            let val (defs, t) = elaborateType env t
            in elaborateAsExists env (Exists (Vector.fromList defs, t)) expr
            end
         | CTerm.Type (pos, t) =>
            let val (defs, body) = elaborateType env t
                val t = FType.Exists (Vector.fromList defs, body)
            in (Pure, FType.Type t, FTerm.Type (pos, t))
            end
         | CTerm.Use (pos, name) =>
            let val def = case lookupValType expr name env
                          of SOME def => def
                           | NONE => ( Env.error env (UnboundVal (pos, name))
                                     ; { pos, id = DefId.fresh (), var = name
                                       , typ = FType.SVar (FType.UVar (Env.freshUv env Predicative)) } )
            in (Pure, #typ def, FTerm.Use (pos, def))
            end
         | CTerm.Const (pos, c) =>
            (Pure, FType.Prim (Const.typeOf c), FTerm.Const (pos, c))

    and elaborateRecord env pos ({fields, ext}: CTerm.row): effect * concr * FTerm.expr =
        let fun elaborateField ((label, expr), (eff, rowType, fieldExprs)) =
                let val pos = CTerm.exprPos expr
                    val (fieldEff, fieldt, expr) = elaborateExpr env expr
                in ( joinEffs (eff, fieldEff)
                   , FType.RowExt {field = (label, fieldt), ext = rowType}
                   , (label, expr) :: fieldExprs )
                end
            val (extEff, extType, extExpr) =
                case ext
                of SOME ext => let val (extEff, t, ext) = elaborateExpr env ext
                               in case t
                                  of FType.Record row => (extEff, row, SOME ext)
                               end
                 | NONE => (Pure, FType.EmptyRow, NONE)
            val (fieldsEff, rowType, fieldExprs) = Vector.foldr elaborateField (Pure, extType, []) fields
            val eff = joinEffs (fieldsEff, extEff)
            val typ = FType.Record rowType
        in (extEff, typ, FTerm.Extend (pos, typ, Vector.fromList fieldExprs, extExpr))
        end

    (* Elaborate the expression `exprRef` to a subtype of `typ`. *)
    and elaborateExprAs (env: Env.t) (typ: concr) (expr: CTerm.expr): effect * FTerm.expr =
        case expr
        of CTerm.Fn (pos, expl, clauses) => (* TODO: Exhaustiveness checking: *)
            (case typ
             of FType.ForAll args => elaborateAsForAll env args expr
              | FType.Arrow (expl', {domain, codomain}) =>
                 ( case (expl, expl')
                   of (Implicit, Implicit) | (Explicit (), Explicit _) => ()
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
                            | (Explicit eff', _) => (subEffect env pos (eff, eff'); expl')
                   in ( Pure
                      , FTerm.Fn ( pos, Scope.Id.fresh (), def, arr
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
             of FType.ForAll args => elaborateAsForAll env args expr
              | _ => coerceExprTo env typ expr)

    and elaborateAsForAll env (params, body) expr =
        let val scopeId = Scope.Id.fresh ()
            val env = Env.pushScope env (Scope.ForAllScope (scopeId, Bindings.Type.fromDefs params))
            val (eff, expr) = elaborateExprAs env body expr
        in (eff, FTerm.TFn (FTerm.exprPos expr, scopeId, params, expr))
        end

    (* Should we start elaboration from more annotated patterns, to enable e.g.
       `{| x -> ... | a: type -> ...}` ? *)
    and elaborateClauses env elaborateBody clauses =
        let fun elaborateClause ({pattern, body}, (matcheeTyp, eff, forallScopeId, clauses)) =
                let val (matcheeTyp, pattern, forallScopeId, env) =
                        case matcheeTyp
                        of SOME (typeDefs, matcheeTyp') =>
                            let val scopeId = getOpt (forallScopeId, Scope.Id.fresh ())
                                val env = Env.pushScope env (Scope.ForAllScope ( scopeId
                                                                               , Bindings.Type.fromDefs typeDefs ))
                                val (pattern, env) = elaboratePatternAs env matcheeTyp' pattern
                            in (matcheeTyp, pattern, SOME scopeId, env)
                            end
                         | NONE =>
                            let val (matcheeTyp, pattern, forallScopeId, env) = elaboratePattern env pattern
                            in (SOME matcheeTyp, pattern, forallScopeId, env)
                            end
                    val (bodyEff, body) = elaborateBody (env, body)
                in (matcheeTyp, joinEffs (eff, bodyEff), forallScopeId, {pattern, body} :: clauses)
                end
            val (matcheeTyp, eff, forallScopeId, clauses) = Vector.foldl elaborateClause (NONE, Pure, NONE, []) clauses
        in (eff, valOf forallScopeId, matcheeTyp, Vector.fromList (List.rev clauses))
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

    and elaboratePattern env =
        fn CTerm.AnnP (pos, {pat = pat as CTerm.Def (pos', name), typ}) =>
            let val (typeDefs, t) = elaborateType env typ
                val def = {pos, id = DefId.fresh (), var = name, typ = t}
                val typeDefs = Vector.fromList typeDefs
                val forallScopeId = Scope.Id.fresh ()
                val env = Env.pushScope env (Scope.ForAllScope (forallScopeId, Bindings.Type.fromDefs typeDefs))
                val patScopeId = Scope.Id.fresh ()
                val env = Env.pushScope env (Scope.PatternScope (patScopeId, name, Visited (def, NONE)))
            in ((typeDefs, t), FTerm.Def (pos', patScopeId, def), SOME forallScopeId, env)
            end
         | CTerm.Def (pos, name) =>
            let val scopeId = Scope.Id.fresh ()
                val t = FType.SVar (FType.UVar (TypeVars.Uv.fresh (scopeId, Predicative)))
                val def = {pos, id = DefId.fresh (), var = name, typ = t}
                val env = Env.pushScope env (Scope.PatternScope (scopeId, name, Visited (def, NONE)))
            in ((#[], t), FTerm.Def (pos, scopeId, def), NONE, env)
            end
         | CTerm.ConstP (pos, c) =>
            let val cTyp = FType.Prim (Const.typeOf c)
            in ((#[], cTyp), FTerm.ConstP (pos, c), NONE, env)
            end

    and elaboratePatternAs env t =
        fn CTerm.AnnP (pos, {pat, typ}) => raise Fail "unimplemented"
         | CTerm.Def (pos, name) =>
            let val scopeId = Scope.Id.fresh ()
                val def = {pos, id = DefId.fresh (), var = name, typ = t}
            in ( FTerm.Def (pos, scopeId, def)
               , Env.pushScope env (Scope.PatternScope (Scope.Id.fresh (), name, Visited (def, NONE))) )
            end
         | CTerm.ConstP (pos, c) =>
            let val cTyp = FType.Prim (Const.typeOf c)
                val _ = unify env pos (cTyp, t)
            in (FTerm.ConstP (pos, c), env)
            end

    and elaborateAsExists env t expr: effect * concr * FTerm.expr =
        let val tWithCtx as (t, _) = instantiateExistential env t
            val (eff, expr) = elaborateAsExistsInst env tWithCtx expr
        in (eff, t, expr)
        end

    and instantiateExistential env (Exists (params: FType.def vector, body)): concr * concr vector = 
        let val paths = Vector.map (fn {var, kind} =>
                                        let val typeFnName = Env.freshAbstract env var {paramKinds = #[], kind}
                                            val typeFn = FType.CallTFn (typeFnName, #[])
                                        in FAst.Type.SVar (FType.Path (Path.new typeFn))
                                        end)
                                   params
           
            val mapping = (params, paths)
                        |> Vector.zipWith (fn ({var, ...}, path) => (var, path))
                        |> Id.SortedMap.fromVector
            val implType = Concr.substitute (Env.hasScope env) mapping body
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
                val coercionNames = Vector.map (fn FAst.Type.SVar (FType.Path path) =>
                                                    let val name = Name.freshen (Name.fromString "coImpl")
                                                        do Path.addScope (path, scopeId, name)
                                                    in name
                                                    end)
                                               paths
                val (eff, expr) = elaborateExprAs env implType expr
                val axiomStmts =
                    Vector.zipWith (fn (FAst.Type.SVar (FType.Path path), name) =>
                                        let val face = Path.face path
                                            val ((params, t), _) = Either.unwrap (Path.get (Env.hasScope env) path)
                                            val args = Vector.map (fn def => FType.UseT def) params
                                        in FTerm.Axiom ( pos, name
                                                       , FType.ForAll (params, FType.app {callee = face, args})
                                                       , FType.ForAll (params, t) )
                                        end)    
                                   (paths, coercionNames)
            in (eff, FTerm.Let (pos, scopeId, axiomStmts, expr))
            end

    (* Like `elaborateExprAs`, but will always just do subtyping and apply the coercion. *)
    and coerceExprTo (env: Env.t) (typ: concr) (expr: CTerm.expr): effect * FTerm.expr =
        let val (eff, t', fexpr) = elaborateExpr env expr
            val coercion = subType env (CTerm.exprPos expr) (t', typ)
        in (eff, applyCoercion coercion fexpr)
        end

    and elaborateStmts env stmts =
        let val (eff, revStmts) =
                Vector.foldl (fn (stmt, (stmtsEff, stmts)) =>
                                  let val (eff, stmt) = elaborateStmt env stmt
                                  in (joinEffs (stmtsEff, eff), stmt :: stmts)
                                  end)
                             (Pure, []) stmts
        in (eff, Vector.fromList (List.rev revStmts))
        end

    (* Elaborate a statement and return the elaborated version. *)
    and elaborateStmt env: Cst.Term.stmt -> effect * FTerm.stmt =
        fn CTerm.Val (pos, pat, expr) =>
            let val rec patName =
                    fn CTerm.Def (_, name) => name
                     | CTerm.AnnP (_, {pat, ...}) => patName pat
                val name = patName pat
                val def as {typ = t, ...} = valOf (lookupValType expr name env) (* `name` is in `env` by construction *)
                val (eff, expr) =
                    case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                    of Unvisited _ | Visiting _ => raise Fail "unreachable" (* Not possible after `lookupValType`. *)
                     | Typed ({typ = (_, ctx), ...}, SOME expr) =>
                        (case ctx
                         of SOME namedPaths => elaborateAsExistsInst env (t, namedPaths) expr
                          | NONE => elaborateExprAs env t expr)
                     | Visited (_, SOME effxpr) => effxpr
                     | Typed (_, NONE) | Visited (_, NONE) => raise Fail "unreachable"
            in (eff, FTerm.Val (pos, def, expr))
            end
         | CTerm.Expr expr =>
            let val (eff, expr) = elaborateExprAs env (FType.Prim FType.Prim.Unit) expr
            in (eff, FTerm.Expr expr)
            end

    (* Coerce `callee` into a function and return t coerced and its `domain` and `codomain`. *)
    and coerceCallee (env: Env.t) (typ: concr, callee: FTerm.expr) : FTerm.expr * effect * {domain: concr, codomain: concr} =
        let fun coerce callee =
                fn FType.ForAll (params, t) =>
                    let val pos = FTerm.exprPos callee
                        val (args, mapping) =
                            Vector.foldl (fn ({var, kind = kind as FType.CallsiteK}, (args, mapping)) =>
                                              let val callId =
                                                      case valOf (FType.piEffect t)
                                                      of Impure =>
                                                          Env.freshAbstract env (FType.Id.fresh ()) {paramKinds = #[], kind}
                                                       | Pure => Env.pureCallsite env
                                                  val callsite = FType.CallTFn (callId, #[])
                                              in (callsite :: args, Id.SortedMap.insert (mapping, var, callsite))
                                              end
                                           | ({var, kind}, (args, mapping)) =>
                                              let val uv = FType.SVar (FType.UVar (Env.newUv env (Predicative, nameFromId var)))
                                              in (uv :: args, Id.SortedMap.insert (mapping, var, uv))
                                              end)
                                         ([], Id.SortedMap.empty) params
                        val args = args |> List.rev |> Vector.fromList
                        val calleeType = Concr.substitute (Env.hasScope env) mapping t
                    in coerce (FTerm.TApp (pos, calleeType, {callee, args})) calleeType
                    end
                 | FType.Arrow (Implicit, {domain, codomain}) =>
                    (case domain
                     of FType.Type domain =>
                         let val pos = FTerm.exprPos callee
                             val arg = FTerm.Type (pos, domain)
                         in coerce (FTerm.App (pos, codomain, {callee, arg})) codomain
                         end
                      | _ => raise Fail "implicit parameter not of type `type`")
                 | FType.Arrow (Explicit eff, domains) => (callee, eff, domains)
                 | FType.SVar (FType.UVar uv) =>
                    (case Uv.get uv
                     of Left uv =>
                         let val domainUv = TypeVars.Uv.freshSibling (uv, Predicative)
                             val codomainUv = TypeVars.Uv.freshSibling (uv, Predicative)
                             val eff = Impure
                             val arrow = { domain = FType.SVar (FType.UVar domainUv)
                                         , codomain = FType.SVar (FType.UVar codomainUv) }
                         in uvSet env (uv, FType.Arrow (Explicit eff, arrow))
                          ; (callee, eff, arrow)
                         end
                      | Right typ => coerce callee typ)
                 | _ => ( Env.error env (UnCallable (callee, typ))
                        ; (callee, Impure, { domain = FType.SVar (FType.UVar (Env.freshUv env Predicative))
                                           , codomain = typ }) )
        in coerce callee typ
        end
   
    (* Coerce `expr` (in place) into a record with at least `label` and return the expr and `label`:ed type. *)
    and coerceRecord env (typ: concr, expr: FTerm.expr) label: FTerm.expr * concr =
        let fun coerce expr = 
                fn FType.ForAll _ => raise Fail "unimplemented"
                 | FType.Arrow (Implicit, {domain, codomain}) =>
                    (case domain
                     of FType.Type domain =>
                         let val pos = FTerm.exprPos expr
                             val arg = FTerm.Type (pos, domain)
                         in coerce (FTerm.App (pos, codomain, {callee = expr, arg})) codomain
                         end
                      | _ => raise Fail "implicit parameter not of type `type`")
                 | FType.Record row => coerceRow expr row
                 | FType.SVar (FType.UVar uv) =>
                    (case Uv.get uv
                     of Right typ => coerce expr typ
                      | Left uv => let val fieldType = FType.SVar (FType.UVar (Env.freshUv env Predicative))
                                       val ext = FType.SVar (FType.UVar (Env.freshUv env Predicative))
                                       val pos = FTerm.exprPos expr
                                       val row = FType.RowExt ({field = (label, fieldType), ext})
                                       val typ = FType.Record row
                                   in uvSet env (uv, typ)
                                    ; (expr, fieldType)
                                   end)
                 | _ => ( Env.error env (UnDottable (expr, typ))
                        ; (expr, FType.SVar (FType.UVar (Env.freshUv env Predicative))) )
            and coerceRow expr =
                fn FType.RowExt ({field = (label', fieldt), ext}) =>
                    if label' = label
                    then (expr, fieldt)
                    else coerceRow expr ext
        in coerce expr typ
        end

    (* TODO: Prevent boundless deepening of REPL env
             and enable forward decl:s for stmts to be input on later lines. *)
    fun elaborateProgram env stmts =
        let val scope = stmtsScope stmts
            val env = Env.pushScope env scope
            val (eff, stmts) = elaborateStmts env stmts
            val program = { typeFns = Env.typeFns env
                          , axioms = Env.axioms env
                          , scope = Scope.id scope
                          , stmts }
        in case Env.errors env
           of [] => Right (program, env)
            | errors => Left (program, env, errors)
        end
end

