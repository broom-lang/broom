structure Typechecker :> sig
    val elaborateProgram: TypecheckingEnv.t -> Cst.Term.stmt vector -> FlexFAst.Term.stmt vector * TypecheckingEnv.t
end = struct
    val op|> = Fn.|>
    datatype predicativity = datatype TypeVars.predicativity
    structure CTerm = Cst.Term
    structure CType = Cst.Type
    structure FTerm = FAst.Term
    structure FType = FAst.Type
    datatype abs = datatype FType.abs
    val concr = FType.Abs.concr

    open TypeError

    structure Env = TypecheckingEnv
    datatype expr_binding_state = datatype Env.Bindings.Expr.binding_state
 
    val subType = Subtyping.subType
    val applyCoercion = Subtyping.applyCoercion

    fun uvSet env =
        TypeVars.Uv.set FlexFAst.Type.Concr.tryToUv Env.Scope.Id.compare (Env.hasScope env)

(* Looking up `val` types *)

    fun unvisitedBindingType pos env name args =
        let do Env.updateExpr pos env name (Fn.constantly (Visiting args)) (* Mark binding 'grey'. *)
            val (t, binding') =
                case args
                of (SOME t, oexpr) =>
                    (case elaborateType env t
                     of ([], t) => (t, Typed (t, oexpr)))
                 | (NONE, SOME expr) =>
                    let val (t, expr) = elaborateExpr env expr
                    in (t, Visited (t, SOME expr))
                    end
                 | (NONE, oexpr as NONE) =>
                    let val t = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
                    in (t, Typed (t, oexpr))
                    end
        in case valOf (Env.findExpr env name)
           of Unvisited _ => raise Fail "unreachable" (* State is at 'least' `Visiting`. *)
            | Visiting _ =>
               ( Env.updateExpr pos env name (Fn.constantly binding')
                ; t )
            | Typed (usageTyp, _) | Visited (usageTyp, _) =>
               (* We must have found a cycle and used `cyclicBindingType`. *)
               ( ignore (subType env pos (t, usageTyp))
               ; usageTyp )
        end
      
    (* In case we encounter a recursive reference to `name` not broken by type annotations we call
       this to insert a unification variable, inferring a monomorphic type. *)
    and cyclicBindingType pos env name (_, oexpr) =
        let val t = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
        in Env.updateExpr pos env name (Fn.constantly (Typed (t, oexpr)))
         ; t
        end

    (* Get the type of the variable `name`, referenced at `pos`, from `env` by either
       - finding the type annotation (if available) (and elaborating it if not already done)
       - elaborating the expression bound to the variable (if available)
       - returning a fresh unification variable (if neither type annotation nor bound expression
         is available or if a cycle is encountered) *)
    and lookupValType expr name env: FlexFAst.Type.concr option =
        Option.map (fn (Unvisited args, env) => unvisitedBindingType (CTerm.exprPos expr) env name args
                     | (Visiting args, env) => cyclicBindingType (CTerm.exprPos expr) env name args
                     | (Typed (t, _) | Visited (t, _), _) => t)
                   (Env.findExprClosure env name)

(* Elaborating subtrees *)

    (* Elaborate the type `typ` and return the elaborated version. *)
    and elaborateType (env: Env.t) (t: CType.typ): FType.def list * FlexFAst.Type.concr =
        let val absBindings = Env.Bindings.Type.new ()
            val absScope = Env.Scope.ExistsScope (Env.Scope.Id.fresh (), absBindings)
            val env = Env.pushScope env absScope

            val rec reAbstract =
                fn Exists (_, #[], t) => t
                 | Exists (pos, params, body) =>
                    let val mapping =
                            Vector.foldl (fn ({var, kind}, mapping) =>
                                              let val id' = Env.Bindings.Type.fresh absBindings kind
                                              in Id.SortedMap.insert (mapping, var, FType.UseT (pos, {var = id', kind}))
                                              end)
                                         Id.SortedMap.empty params
                    in FlexFAst.Type.Concr.substitute mapping body
                    end

            fun elaborate env =
                fn CType.Pi (pos, {var, typ = domain}, codomain) =>
                    let val (typeDefs, domain) =
                            case domain
                            of SOME domain => elaborateType env domain
                             | NONE => ([], FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative)))

                        val env = List.foldl (fn (def, env) =>
                                                  Env.pushScope env (Env.Scope.ForAllScope (Env.Scope.Id.fresh (), def)))
                                             env typeDefs
                        val fnScope = Env.Scope.FnScope (Env.Scope.Id.fresh (), var, Visited (domain, NONE))
                        val env = Env.pushScope env fnScope

                        val codomain = elaborate env codomain
                    in FType.ForAll ( pos, Vector.fromList typeDefs
                                    , FType.Arrow (pos, {domain, codomain}) )
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
                        val var = Env.Bindings.Type.fresh absBindings kind
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
                     of FType.Type (_, t) => reAbstract t
                      | _ => raise Fail ("Type path " ^ CTerm.exprToString pathExpr
                                         ^ "does not denote type at " ^ Pos.toString (CTerm.exprPos pathExpr)))
                 | CType.TypeT pos =>
                    let val kind = FType.TypeK pos
                        val var = Env.Bindings.Type.fresh absBindings kind
                    in FType.Type (pos, concr (FType.UseT (pos, {var, kind})))
                    end
                 | CType.Singleton (pos, expr) => #1 (elaborateExpr env expr)
                 | CType.Prim (pos, p) => FType.Prim (pos, p)

            and elaborateDecl env (name, t) =
                ( name
                , case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                  of Unvisited args => unvisitedBindingType (CType.pos t) env name args
                   | Visiting args => cyclicBindingType (CType.pos t) env name args
                   | Typed (t, _) | Visited (t, _) => t )

            val t = elaborate env t
            val defs = Env.Bindings.Type.defs absBindings
        in (defs, t)
        end

    and declsScope decls =
        let val builder = Env.Bindings.Expr.Builder.new ()
            do Vector.app (fn (name, t) =>
                                Env.Bindings.Expr.Builder.insert builder name (Unvisited (SOME t, NONE)))
                          decls
        in Env.Scope.BlockScope (Env.Scope.Id.fresh (), Env.Bindings.Expr.Builder.build builder)
        end

    and stmtsScope stmts =
        let val builder = Env.Bindings.Expr.Builder.new ()
            do Vector.app (fn CTerm.Val (_, name, t, expr) =>
                               Env.Bindings.Expr.Builder.insert builder name (Unvisited (t, SOME expr))
                            | CTerm.Expr _ => ())
                          stmts
        in Env.Scope.BlockScope (Env.Scope.Id.fresh (), Env.Bindings.Expr.Builder.build builder)
        end

    (* Elaborate the expression `exprRef` and return its computed type. *)
    and elaborateExpr (env: Env.t) (expr: CTerm.expr): FlexFAst.Type.concr * FlexFAst.Type.sv FTerm.expr =
        case expr
        of CTerm.Fn (pos, var, domain, body) =>
            let val (typeDefs, domain) =
                    case domain
                    of SOME domain => elaborateType env domain
                     | NONE => ([], FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative)))
                val codomain = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))

                val env = List.foldl (fn (def, env) =>
                                          Env.pushScope env (Env.Scope.ForAllScope (Env.Scope.Id.fresh (), def)))
                                     env typeDefs
                val fnScope = Env.Scope.FnScope (Env.Scope.Id.fresh (), var, Visited (domain, NONE))
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
         | CTerm.If (pos, _, _, _) =>
            let val t = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
            in (t, elaborateExprAs env t expr)
            end
         | CTerm.Record (pos, fields) => elaborateRecord env pos fields
         | CTerm.Module (pos, stmts) =>
            let val env = Env.pushScope env (stmtsScope stmts)
                val stmts = Vector.map (elaborateStmt env) stmts
                val defs = Vector.foldr (fn (FTerm.Val (_, def, _), defs) => def :: defs
                                          | (FTerm.Expr _, defs) => defs)
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
            let val ct as (_, callee) = elaborateExpr env callee
                val (callee, {domain, codomain}) = coerceCallee env ct 
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
            in elaborateAsExists env (pos, Vector.fromList defs, t) expr
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

    and elaborateRecord env pos ({fields, ext}: CTerm.row): FlexFAst.Type.concr * FlexFAst.Type.sv FTerm.expr =
        let fun elaborateField (field as (label, expr), (rowType, fieldExprs)) =
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
    and elaborateExprAs (env: Env.t) (typ: FlexFAst.Type.concr) (expr: CTerm.expr): FlexFAst.Type.sv FTerm.expr =
        case expr
        of CTerm.Fn (pos, param, paramType, body) =>
            (case typ
             of FType.ForAll args => elaborateAsForAll env args expr
              | FType.Arrow (_, {domain, codomain}) =>
                 (case paramType
                  of NONE =>
                      let val env =
                              Env.pushScope env (Env.Scope.FnScope (Env.Scope.Id.fresh (), param, Visited (domain, NONE)))
                          val body = elaborateExprAs env codomain body
                      in FTerm.Fn (pos, {var = param, typ = domain}, body)
                      end)
              | _ => coerceExprTo env typ expr)
         | CTerm.If (pos, cond, conseq, alt) =>
            FTerm.If (pos, elaborateExprAs env (FType.Prim (pos, FType.Prim.Bool)) cond
                         , elaborateExprAs env typ conseq
                         , elaborateExprAs env typ alt )
         | _ =>
            (case typ
             of FType.ForAll args => elaborateAsForAll env args expr
              | _ => coerceExprTo env typ expr)

    and elaborateAsForAll env (pos, params, body) expr =
        let val env =
                Vector.foldl (fn (def, env) =>
                                  Env.pushScope env (Env.Scope.ForAllScope (Env.Scope.Id.fresh (), def)))
                             env params
        in FTerm.TFn (pos, params, elaborateExprAs env body expr)
        end

    and elaborateAsExists env (pos, params: FType.def vector, body) expr =
        let val coScopeId = Env.Scope.Id.fresh ()
            val coScope = Env.Scope.Marker coScopeId

            val typeFnArgs = Vector.map (fn def => FType.UseT (pos, def)) (Env.bigLambdaParams env)
            val typeFns = Vector.map (Env.freshAbstract env (Vector.length typeFnArgs)) params
            val axiomNames = Vector.map (fn typeFnName =>
                                             Name.toString typeFnName ^ "Impl"
                                                 |> Name.fromString
                                                 |> Name.freshen)
                                        typeFns
            val paths = Vector.map (fn (typeFn, coName) =>
                                        let val path = TypeVars.Path.new ( FType.CallTFn (pos, typeFn, typeFnArgs)
                                                                         , coScopeId, coName )
                                        in FAst.Type.SVar (pos, FlexFAst.Type.Path path)
                                        end)
                                   (Vector.zip (typeFns, axiomNames))
            val namedPaths = Vector.zip (axiomNames, paths)
           
            val mapping = Vector.foldl (fn (({var, ...}, path), mapping) =>
                                            Id.SortedMap.insert (mapping, var, path))
                                       Id.SortedMap.empty
                                       (Vector.zip (params, paths))
            val implType = FlexFAst.Type.Concr.substitute mapping body
            val pos = CTerm.exprPos expr
        in ( implType
           , FTerm.Let ( pos
                       , Vector.map (fn (name, co) => FTerm.Axiom (pos, name, co)) namedPaths
                       , elaborateExprAs (Env.pushScope env coScope) implType expr ) )
        end

    (* Like `elaborateExprAs`, but will always just do subtyping and apply the coercion. *)
    and coerceExprTo (env: Env.t) (typ: FlexFAst.Type.concr) (expr: CTerm.expr): FlexFAst.Type.sv FTerm.expr =
        let val (t', fexpr) = elaborateExpr env expr
            val coercion = subType env (CTerm.exprPos expr) (t', typ)
        in applyCoercion coercion fexpr
        end

    (* Elaborate a statement and return the elaborated version. *)
    and elaborateStmt env: Cst.Term.stmt -> FlexFAst.Type.sv FTerm.stmt =
        fn CTerm.Val (pos, name, _, expr) =>
            let val t = valOf (lookupValType expr name env) (* `name` is in `env` by construction *)
                val expr =
                    case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                    of Unvisited _ | Visiting _ => raise Fail "unreachable" (* Not possible after `lookupValType`. *)
                     | Typed (_, SOME expr) => elaborateExprAs env t expr
                     | Visited (_, SOME expr) => expr
                     | Typed (_, NONE) | Visited (_, NONE) => raise Fail "unreachable"
            in FTerm.Val (pos, {var = name, typ = t}, expr)
            end
         | CTerm.Expr expr => FTerm.Expr (elaborateExprAs env (FType.unit (CTerm.exprPos expr)) expr)

    (* Coerce `callee` into a function and return t coerced and its `domain` and `codomain`. *)
    and coerceCallee (env: Env.t) (typ: FlexFAst.Type.concr, callee: FlexFAst.Term.expr)
      : FlexFAst.Term.expr * {domain: FlexFAst.Type.concr, codomain: FlexFAst.Type.concr} =
        let fun coerce callee =
                fn FType.ForAll (_, params, t) =>
                    let val pos = FTerm.exprPos callee
                        val mapping =
                            Vector.foldl (fn ({var, kind}, mapping) =>
                                              let val uv = FType.SVar (pos, FlexFAst.Type.UVar (Env.newUv env (Predicative, Name.fromId var)))
                                              in Id.SortedMap.insert (mapping, var, uv)
                                              end)
                                         Id.SortedMap.empty params
                        val args = Id.SortedMap.listItems mapping |> Vector.fromList
                        val calleeType = FlexFAst.Type.Concr.substitute mapping t
                    in coerce (FTerm.TApp (pos, calleeType, {callee, args})) calleeType
                    end
                 | FType.Arrow (_, domains) => (callee, domains)
                 | FType.SVar (_, FlexFAst.Type.UVar uv) =>
                    (case TypeVars.Uv.get uv
                     of Either.Left uv => raise Fail "unimplemented"
                      | Either.Right typ => coerce callee typ)
                 | _ => raise TypeError (UnCallable (callee, typ))
        in coerce callee typ
        end
   
    (* Coerce `expr` (in place) into a record with at least `label` and return the `label`:ed type. *)
    and coerceRecord env (typ: FlexFAst.Type.concr, expr: FlexFAst.Type.sv FTerm.expr) label: FlexFAst.Type.concr =
        let val rec coerce =
                fn FType.ForAll _ => raise Fail "unimplemented"
                 | FType.Record (_, row) => coerceRow row
                 | FType.SVar (pos, FlexFAst.Type.UVar uv) =>
                    (case TypeVars.Uv.get uv
                     of Either.Right typ => coerce typ
                      | Either.Left uv => let val fieldType = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
                                              val ext = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
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
            val stmts = Vector.map (elaborateStmt env) stmts
        in (stmts, env)
        end
end

