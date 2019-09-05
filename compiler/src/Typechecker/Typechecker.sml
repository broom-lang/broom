structure Typechecker :> sig
    val elaborateProgram: TypecheckingEnv.t -> Cst.Term.stmt vector -> FlexFAst.Term.program * TypecheckingEnv.t
end = struct
    val op|> = Fn.|>
    datatype either = datatype Either.t
    structure Uv = TypeVars.Uv
    datatype predicativity = datatype TypeVars.predicativity
    structure CTerm = Cst.Term
    structure CType = Cst.Type
    structure FAst = FlexFAst
    structure FTerm = FAst.Term
    structure FType = FAst.Type
    structure Id = FType.Id
    structure Concr = FType.Concr
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
    val subType = Subtyping.subType
    val unify = Subtyping.unify

    fun uvSet env =
        Uv.set Concr.tryToUv Scope.Id.compare (Env.hasScope env)

    val nameFromId = Name.fromString o Id.toString

(* Looking up statement/declaration types *)

    fun unvisitedBindingType pos env name args =
        let do Env.updateExpr pos env name (Fn.constantly (Visiting args)) (* Mark binding 'grey'. *)
            val (t, binding') =
                case args
                of (SOME t, oexpr) =>
                    (case elaborateType env t
                     of ([], t) => (t, Typed (t, NONE, oexpr))
                      | (defs, t) =>
                         (case valOf (Env.innermostScope env)
                          of Scope.InterfaceScope _ =>
                              let val abst = Exists (pos, Vector.fromList defs, t)
                                  val t = reAbstract env abst (* OPTIMIZE *)
                              in (t, Typed (t, NONE, oexpr))
                              end
                           | _ =>
                              let val (t, paths) =
                                      instantiateExistential env (Exists (pos, Vector.fromList defs, t))
                              in (t, Typed (t, SOME paths, oexpr))
                              end))
                 | (NONE, SOME expr) =>
                    let val (t, expr) = elaborateExpr env expr
                    in (t, Visited (t, SOME expr))
                    end
                 | (NONE, oexpr as NONE) =>
                    let val t = FType.SVar (pos, FType.UVar (Env.freshUv env Predicative))
                    in (t, Typed (t, NONE, oexpr))
                    end
        in case valOf (Env.findExpr env name)
           of Unvisited _ => raise Fail "unreachable" (* State is at 'least' `Visiting`. *)
            | Visiting _ =>
               ( Env.updateExpr pos env name (Fn.constantly binding')
               ; t )
            | Typed (usageTyp, NONE, _) | Visited (usageTyp, _) =>
               (* We must have found a cycle and used `cyclicBindingType`. *)
               ( ignore (subType env pos (t, usageTyp))
               ; usageTyp )
            | Typed (_, SOME _, _) => raise Fail "unreachable"
        end
      
    (* In case we encounter a recursive reference to `name` not broken by type annotations we call
       this to insert a unification variable, inferring a monomorphic type. *)
    and cyclicBindingType pos env name (_, oexpr) =
        let val t = FType.SVar (pos, FType.UVar (Env.freshUv env Predicative))
        in Env.updateExpr pos env name (Fn.constantly (Typed (t, NONE, oexpr)))
         ; t
        end

    (* Get the type of the variable `name`, referenced at `pos`, from `env` by either
       - finding the type annotation (if available) (and elaborating it if not already done)
       - elaborating the expression bound to the variable (if available)
       - returning a fresh unification variable (if neither type annotation nor bound expression
         is available or if a cycle is encountered) *)
    and lookupValType expr name env: concr option =
        Option.map (fn (Unvisited args, env) => unvisitedBindingType (CTerm.exprPos expr) env name args
                     | (Visiting args, env) =>
                        let val pos = CTerm.exprPos expr
                        in case valOf (Env.innermostScope env)
                           of Scope.InterfaceScope _ => raise Fail ("Type cycle at " ^ Pos.toString pos)
                            | _ => cyclicBindingType pos env name args
                        end
                     | (Typed (t, _, _) | Visited (t, _), _) => t)
                   (Env.findExprClosure env name)

    and reAbstract env =
        fn Exists (pos, params, body) =>
            let val (_, absBindings) = valOf (Env.nearestExists env)
                val mapping =
                    Vector.foldl (fn ({var, kind}, mapping) =>
                                      let val id' = Bindings.Type.fresh absBindings kind
                                      in Id.SortedMap.insert (mapping, var, FType.UseT (pos, {var = id', kind}))
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
                fn CType.Pi (pos, {var, typ = domain}, codomain) =>
                    let val (typeDefs, domain) =
                            case domain
                            of SOME domain => elaborateType env domain
                             | NONE => ([], FType.SVar (pos, FType.UVar (Env.freshUv env Predicative)))

                        val env = Env.pushScope env (Scope.ForAllScope ( Scope.Id.fresh ()
                                                                       , typeDefs |> Vector.fromList |> Bindings.Type.fromDefs ))
                        val fnScope = Scope.FnScope (Scope.Id.fresh (), var, Visited (domain, NONE))
                        val env = Env.pushScope env fnScope

                        val codomain = elaborate env codomain
                        val arrow = FType.Arrow (pos, {domain, codomain})
                    in case typeDefs
                       of [] => arrow
                        | _ => FType.ForAll (pos, Vector.fromList typeDefs, arrow)
                    end
                 | CType.RecordT (pos, row) => FType.Record (pos, elaborate env row)
                 | CType.RowExt (pos, {fields, ext}) =>
                    let fun step ((label, t), ext) =
                            FType.RowExt (pos, {field = (label, elaborate env t), ext})
                    in Vector.foldr step (elaborate env ext) fields
                    end
                 | CType.EmptyRow pos => FType.EmptyRow pos
                 | CType.WildRow pos =>
                    let val kind = FType.RowK pos
                        val var = Bindings.Type.fresh absBindings kind
                    in FType.UseT (pos, {var, kind})
                    end
                 | CType.Interface (pos, decls) =>
                    let val env = Env.pushScope env (declsScope decls)
                        val fields = Vector.map (elaborateDecl env) decls
                        fun constructStep (field, ext) = FType.RowExt (pos, {field, ext})
                    in FType.Record (pos, Vector.foldr constructStep (FType.EmptyRow pos) fields)
                    end
                 | CType.Path pathExpr =>
                    (case #1 (elaborateExpr env pathExpr)
                     of FType.Type (_, t) => reAbstract env t
                      | _ => raise Fail ("Type path " ^ CTerm.exprToString pathExpr
                                         ^ "does not denote type at " ^ Pos.toString (CTerm.exprPos pathExpr)))
                 | CType.TypeT pos =>
                    let val kind = FType.TypeK pos
                        val var = Bindings.Type.fresh absBindings kind
                    in FType.Type (pos, concr (FType.UseT (pos, {var, kind})))
                    end
                 | CType.Singleton (_, expr) => #1 (elaborateExpr env expr)
                 | CType.Prim (pos, p) => FType.Prim (pos, p)

            and elaborateDecl env (name, t) =
                ( name
                , case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                  of Unvisited args => unvisitedBindingType (CType.pos t) env name args
                   | Visiting _ => raise Fail ("Type cycle at " ^ Pos.toString (CType.pos t))
                   | Typed (t, _, _) | Visited (t, _) => t )

            val t = elaborate env t
            val defs = Bindings.Type.defs absBindings
        in (defs, t)
        end

    and declsScope decls =
        let val builder = Bindings.Expr.Builder.new ()
            do Vector.app (fn (name, t) =>
                                Bindings.Expr.Builder.insert builder name (Unvisited (SOME t, NONE)))
                          decls
        in Scope.InterfaceScope (Scope.Id.fresh (), Bindings.Expr.Builder.build builder)
        end

    and stmtsScope stmts =
        let val builder = Bindings.Expr.Builder.new ()
            do Vector.app (fn CTerm.Val (_, CTerm.Def (_, name), expr) =>
                               Bindings.Expr.Builder.insert builder name (Unvisited (NONE, SOME expr))
                            | CTerm.Val (_, CTerm.AnnP (_, {pat = CTerm.Def (_, name), typ}), expr) =>
                               Bindings.Expr.Builder.insert builder name (Unvisited (SOME typ, SOME expr))
                            | CTerm.Expr _ => ())
                          stmts
        in Scope.BlockScope (Scope.Id.fresh (), Bindings.Expr.Builder.build builder)
        end

    (* Elaborate the expression `exprRef` and return its computed type. *)
    and elaborateExpr (env: Env.t) (expr: CTerm.expr): concr * FTerm.expr =
        case expr
        of CTerm.Fn (pos, {var, typ = domain}, body) =>
            let val (typeDefs, domain) =
                    case domain
                    of SOME domain => elaborateType env domain
                     | NONE => ([], FType.SVar (pos, FType.UVar (Env.freshUv env Predicative)))
                val codomain = FType.SVar (pos, FType.UVar (Env.freshUv env Predicative))

                val env = Env.pushScope env (Scope.ForAllScope ( Scope.Id.fresh ()
                                                               , typeDefs |> Vector.fromList |> Bindings.Type.fromDefs ))
                val fnScope = Scope.FnScope (Scope.Id.fresh (), var, Visited (domain, NONE))
                val env = Env.pushScope env fnScope

                val params = Vector.fromList typeDefs
                val body = elaborateExprAs env codomain body
            in ( let val arrow = FType.Arrow (pos, {domain, codomain})
                 in case params
                    of #[] => arrow
                     | _ => FType.ForAll (pos, params, arrow)
                 end
               , let val f = FTerm.Fn (pos, {var, typ = domain}, body)
                 in case params
                    of #[] => f
                     | _ => FTerm.TFn (pos, params, f)
                 end )
            end
         | CTerm.Let (pos, stmts, body) =>
            let val env = Env.pushScope env (stmtsScope stmts)
                val stmts = Vector.map (elaborateStmt env) stmts
                val (typ, body) = elaborateExpr env body
            in (typ, FTerm.Let (pos, stmts, body))
            end
         | CTerm.Match (pos, _, _) =>
            let val t = FType.SVar (pos, FType.UVar (Env.freshUv env Predicative))
            in (t, elaborateExprAs env t expr)
            end
         (* TODO: Descend into subcomponents of records and modules so that e.g.
                  `module val id = fn _ => fn x => x end : interface val id: fun a: type => a -> a end`
                  will work. It would also avoid an intermediate record in the elaborated code. *)
         | CTerm.Record (pos, fields) => elaborateRecord env pos fields
         | CTerm.Module (pos, stmts) =>
            let val env = Env.pushScope env (stmtsScope stmts)
                val stmts = Vector.map (elaborateStmt env) stmts
                val defs = Vector.foldr (fn (FTerm.Val (_, def, _), defs) => def :: defs
                                          | (FTerm.Axiom _, defs) | (FTerm.Expr _, defs) => defs)
                                        [] stmts
                val row = List.foldl (fn ({var, typ}, ext) => FType.RowExt (pos, {field = (var, typ), ext}))
                                     (FType.EmptyRow pos) defs
                val typ = FType.Record (pos, row)
                val body = FTerm.Extend ( pos, typ
                                        , Vector.fromList defs
                                              |> Vector.map (fn def as {var, ...} => (var, FTerm.Use (pos, def)))
                                        , NONE )
            in (typ, FTerm.Let (pos, stmts, body))
            end
         | CTerm.App (pos, {callee, arg}) =>
            let val (callee, {domain, codomain}) = coerceCallee env (elaborateExpr env callee)
                val arg = elaborateExprAs env domain arg
            in (codomain, FTerm.App (pos, codomain, {callee, arg}))
            end
         | CTerm.Field (pos, expr, label) =>
            let val te as (_, expr) = elaborateExpr env expr
                val fieldType = coerceRecord env te label
            in (fieldType, FTerm.Field (pos, fieldType, expr, label))
            end
         | CTerm.Ann (pos, expr, t) =>
            let val (defs, t) = elaborateType env t
            in elaborateAsExists env (Exists (pos, Vector.fromList defs, t)) expr
            end
         | CTerm.Type (pos, t) =>
            let val (defs, body) = elaborateType env t
                val t = FType.Exists (pos, Vector.fromList defs, body)
            in (FType.Type (pos, t), FTerm.Type (pos, t))
            end
         | CTerm.Use (pos, name) =>
            let val typ = case lookupValType expr name env
                          of SOME typ => typ
                           | NONE => raise TypeError (UnboundVal (pos, name))
                val def = {var = name, typ}
            in (typ, FTerm.Use (pos, def))
            end
         | CTerm.Const (pos, c) =>
            (FType.Prim (pos, Const.typeOf c), FTerm.Const (pos, c))

    and elaborateRecord env pos ({fields, ext}: CTerm.row): concr * FTerm.expr =
        let fun elaborateField ((label, expr), (rowType, fieldExprs)) =
                let val pos = CTerm.exprPos expr
                    val (fieldt, expr) = elaborateExpr env expr
                in ( FType.RowExt (pos, {field = (label, fieldt), ext = rowType})
                   , (label, expr) :: fieldExprs )
                end
            val (extType, extExpr) = case ext
                                     of SOME ext => let val (t, ext) = elaborateExpr env ext
                                                    in case t
                                                       of FType.Record (_, row) => (row, SOME ext)
                                                    end
                                      | NONE => (FType.EmptyRow pos, NONE)
            val (rowType, fieldExprs) = Vector.foldr elaborateField (extType, []) fields
            val typ = FType.Record (pos, rowType)
        in (typ, FTerm.Extend (pos, typ, Vector.fromList fieldExprs, extExpr))
        end

    (* Elaborate the expression `exprRef` to a subtype of `typ`. *)
    and elaborateExprAs (env: Env.t) (typ: concr) (expr: CTerm.expr): FTerm.expr =
        case expr
        of CTerm.Fn (pos, {var = param, typ = paramType}, body) =>
            (case typ
             of FType.ForAll args => elaborateAsForAll env args expr
              | FType.Arrow (_, {domain, codomain}) =>
                 (case paramType
                  of NONE =>
                      let val env =
                              Env.pushScope env (Scope.FnScope (Scope.Id.fresh (), param, Visited (domain, NONE)))
                          val body = elaborateExprAs env codomain body
                      in FTerm.Fn (pos, {var = param, typ = domain}, body)
                      end)
              | _ => coerceExprTo env typ expr)
         | CTerm.Match (pos, matchee, clauses) => (* TODO: Exhaustiveness checking: *)
            let val (matcheeTyp, matchee) = elaborateExpr env matchee
            in FTerm.Match ( pos, typ, matchee
                           , elaborateClauses env matcheeTyp
                                 (fn (env, body) => elaborateExprAs env typ body)
                                 clauses )
            end
         | _ =>
            (case typ
             of FType.ForAll args => elaborateAsForAll env args expr
              | _ => coerceExprTo env typ expr)

    and elaborateAsForAll env (pos, params, body) expr =
        let val env = Env.pushScope env (Scope.ForAllScope (Scope.Id.fresh (), Bindings.Type.fromDefs params))
        in FTerm.TFn (pos, params, elaborateExprAs env body expr)
        end

    and elaborateClauses env matcheeTyp elaborateBody =
        Vector.map (elaborateClause env matcheeTyp elaborateBody)

    and elaborateClause env matcheeTyp elaborateBody {pattern, body} =
        let val (pattern, env) = elaboratePatternAs env matcheeTyp pattern
            val body = elaborateBody (env, body)
        in {pattern, body}
        end

    and elaboratePatternAs env t =
        fn CTerm.AnnP (pos, {pat, typ}) => raise Fail "unimplemented"
         | CTerm.Def (pos, name) =>
            ( FTerm.Def (pos, name)
            , Env.pushScope env (Scope.PatternScope (Scope.Id.fresh (), name, Visited (t, NONE))) )
         | CTerm.ConstP (pos, c) =>
            let val cTyp = FType.Prim (pos, Const.typeOf c)
                do unify env pos (cTyp, t)
            in (FTerm.ConstP (pos, c), env)
            end

    and elaborateAsExists env t expr: concr * FTerm.expr =
        let val tWithCtx as (t, _) = instantiateExistential env t
        in (t, elaborateAsExistsInst env tWithCtx expr)
        end

    and instantiateExistential env (Exists (pos, params: FType.def vector, body)): concr * concr vector = 
        let val typeFnArgDefs = Env.bigLambdaParams env
            val typeFnArgs = Vector.map (fn def => FType.UseT (pos, def)) typeFnArgDefs
            val paramKinds = Vector.map #kind typeFnArgDefs
            val typeFns = Vector.map (fn {var, kind} => Env.freshAbstract env var {paramKinds, kind})
                                     params
            val paths = Vector.map (fn typeFn =>
                                        let val path = Path.new (FType.CallTFn (pos, typeFn, typeFnArgs))
                                        in FAst.Type.SVar (pos, FType.Path path)
                                        end)
                                   typeFns
           
            val mapping = (params, paths)
                        |> Vector.zipWith (fn ({var, ...}, path) => (var, path))
                        |> Id.SortedMap.fromVector
            val implType = Concr.substitute (Env.hasScope env) mapping body
        in (implType, paths)
        end

    and elaborateAsExistsInst env (implType, paths) =
        fn CTerm.Match (pos, matchee, clauses) =>
            let val (matcheeTyp, matchee) = elaborateExpr env matchee
            in FTerm.Match ( pos, implType, matchee
                           , elaborateClauses env matcheeTyp
                                 (fn (env, body) => elaborateAsExistsInst env (implType, paths) body)
                                 clauses )
            end
         | expr =>
            let val scopeId = Scope.Id.fresh ()
                val env' = Env.pushScope env (Scope.Marker scopeId)
                val pos = CTerm.exprPos expr
                val axiomStmts =
                    Vector.map (fn FAst.Type.SVar (_, FType.Path path) =>
                                    let val name = Name.freshen (Name.fromString "coImpl")
                                        do Path.addScope (path, scopeId, name)
                                        val (face, _) = Either.unwrapLeft (Path.get (Env.hasScope env) path)
                                        val impl = case Path.get (Env.hasScope env') path
                                                   of Either.Left (face, _) => face
                                                    | Either.Right (impl, _) => impl
                                    in FTerm.Axiom (pos, name, face, impl)
                                    end)    
                               paths
                val expr = elaborateExprAs env' implType expr
            in FTerm.Let (pos, axiomStmts, expr)
            end

    (* Like `elaborateExprAs`, but will always just do subtyping and apply the coercion. *)
    and coerceExprTo (env: Env.t) (typ: concr) (expr: CTerm.expr): FTerm.expr =
        let val (t', fexpr) = elaborateExpr env expr
            val coercion = subType env (CTerm.exprPos expr) (t', typ)
        in applyCoercion coercion fexpr
        end

    (* Elaborate a statement and return the elaborated version. *)
    and elaborateStmt env: Cst.Term.stmt -> FTerm.stmt =
        fn CTerm.Val (pos, pat, expr) =>
            let val rec patName =
                    fn CTerm.Def (_, name) => name
                     | CTerm.AnnP (_, {pat, ...}) => patName pat
                val name = patName pat
                val t = valOf (lookupValType expr name env) (* `name` is in `env` by construction *)
                val expr =
                    case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                    of Unvisited _ | Visiting _ => raise Fail "unreachable" (* Not possible after `lookupValType`. *)
                     | Typed (_, ctx, SOME expr) =>
                        (case ctx
                         of SOME namedPaths => elaborateAsExistsInst env (t, namedPaths) expr
                          | NONE => elaborateExprAs env t expr)
                     | Visited (_, SOME expr) => expr
                     | Typed (_, _, NONE) | Visited (_, NONE) => raise Fail "unreachable"
            in FTerm.Val (pos, {var = name, typ = t}, expr)
            end
         | CTerm.Expr expr => FTerm.Expr (elaborateExprAs env (FType.unit (CTerm.exprPos expr)) expr)

    (* Coerce `callee` into a function and return t coerced and its `domain` and `codomain`. *)
    and coerceCallee (env: Env.t) (typ: concr, callee: FTerm.expr) : FTerm.expr * {domain: concr, codomain: concr} =
        let fun coerce callee =
                fn FType.ForAll (_, params, t) =>
                    let val pos = FTerm.exprPos callee
                        val mapping =
                            Vector.foldl (fn ({var, kind}, mapping) =>
                                              let val uv = FType.SVar (pos, FType.UVar (Env.newUv env (Predicative, nameFromId var)))
                                              in Id.SortedMap.insert (mapping, var, uv)
                                              end)
                                         Id.SortedMap.empty params
                        val args = Id.SortedMap.listItems mapping |> Vector.fromList
                        val calleeType = Concr.substitute (Env.hasScope env) mapping t
                    in coerce (FTerm.TApp (pos, calleeType, {callee, args})) calleeType
                    end
                 | FType.Arrow (_, domains) => (callee, domains)
                 | FType.SVar (pos, FType.UVar uv) =>
                    (case Uv.get uv
                     of Left uv =>
                         let val domainUv = TypeVars.Uv.freshSibling (uv, Predicative)
                             val codomainUv = TypeVars.Uv.freshSibling (uv, Predicative)
                             val arrow = { domain = FType.SVar (pos, FType.UVar domainUv)
                                         , codomain = FType.SVar (pos, FType.UVar codomainUv) }
                         in uvSet env (uv, FType.Arrow (pos, arrow))
                          ; (callee, arrow)
                         end
                      | Right typ => coerce callee typ)
                 | _ => raise TypeError (UnCallable (callee, typ))
        in coerce callee typ
        end
   
    (* Coerce `expr` (in place) into a record with at least `label` and return the `label`:ed type. *)
    and coerceRecord env (typ: concr, expr: FTerm.expr) label: concr =
        let val rec coerce =
                fn FType.ForAll _ => raise Fail "unimplemented"
                 | FType.Record (_, row) => coerceRow row
                 | FType.SVar (pos, FType.UVar uv) =>
                    (case Uv.get uv
                     of Right typ => coerce typ
                      | Left uv => let val fieldType = FType.SVar (pos, FType.UVar (Env.freshUv env Predicative))
                                       val ext = FType.SVar (pos, FType.UVar (Env.freshUv env Predicative))
                                       val pos = FTerm.exprPos expr
                                       val row = FType.RowExt (pos, {field = (label, fieldType), ext})
                                       val typ = FType.Record (pos, row)
                                   in uvSet env (uv, typ)
                                    ; fieldType
                                   end)
                 | _ => raise TypeError (UnDottable (expr, typ))
            and coerceRow =
                fn FType.RowExt (_, {field = (label', fieldt), ext}) =>
                    if label' = label
                    then fieldt
                    else coerceRow ext
        in coerce typ
        end

    (* TODO: Prevent boundless deepening of REPL env
             and enable forward decl:s for stmts to be input on later lines. *)
    fun elaborateProgram env stmts =
        let val env = Env.pushScope env (stmtsScope stmts)
            val program = { typeFns = Env.typeFns env
                          , axioms = Env.axioms env
                          , stmts = Vector.map (elaborateStmt env) stmts }
        in (program, env)
        end
end

