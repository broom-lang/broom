structure Typechecker :> sig
    val elaborateExpr: TypecheckingEnv.t -> Cst.Term.expr -> FlexFAst.Type.concr * FlexFAst.Term.expr
end = struct
    datatype predicativity = datatype TypeVars.predicativity
    structure CTerm = Cst.Term
    structure CType = Cst.Type
    structure FTerm = FAst.Term
    structure FType = FAst.Type
    datatype abs = datatype FType.abs

    open TypeError

    structure Env = TypecheckingEnv
    datatype expr_binding_state = datatype Env.Bindings.Expr.binding_state
 
    val subType = Subtyping.subType
    val applyCoercion = Subtyping.applyCoercion

(* Looking up `val` types *)
    fun unvisitedBindingType pos env name args =
        let do Env.updateExpr pos env name (Fn.constantly (Visiting args))
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
           of Unvisited _ => raise Fail "unreachable"
            | Visiting _ =>
               ( Env.updateExpr pos env name (Fn.constantly binding')
                ; t )
            | Typed (usageTyp, _) | Visited (usageTyp, _) =>
               ( ignore (subType env pos (Concr t, Concr usageTyp))
               ; usageTyp )
        end
       
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

            val rec reAbstract = (* OPTIMIZE: nested substitutions *)
                fn Exists (pos, {var = id, kind}, body) =>
                    let val id' = Env.Bindings.Type.fresh absBindings kind
                    in FlexFAst.Type.Concr.substitute (id, FType.UseT (pos, {var = id', kind}))
                                          (reAbstract body)
                    end
                 | Concr t => t

            fun elaborate env =
                fn CType.Pi (pos, {var, typ = domain}, codomain) =>
                    let val (ddefs as [], domain) =
                            case domain
                            of SOME domain => elaborateType env domain
                             | NONE => raise Fail "unimplemented"
                        val fnScope = Env.Scope.FnScope (Env.Scope.Id.fresh (), var, Visited (domain, NONE))
                        val env = Env.pushScope env fnScope
                        val codomain = elaborate env codomain
                    in FType.Arrow (pos, {domain, codomain})
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
                    in FType.Type (pos, Concr (FType.UseT (pos, {var, kind})))
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
        of CTerm.Fn (pos, param, paramType, body) =>
            (*let val (typeDefs, domain) =
                    case !paramType
                    of SOME domain => Pair.second SOME (elaborateType env domain)
                     | NONE => ([], NONE)
                val env = let val fnScope :: env = env
                              fun pushDef ({var, kind}, env) =
                                  let val bindingRef = ref NONE
                                      val scope = FlexFAst.TypeScope (FlexFAst.Scope.forTFn (var, bindingRef))
                                      val env = scope :: env
                                  in bindingRef := SOME {binder = kind, shade = ref FlexFAst.Black}
                                   ; env
                                  end
                          in fnScope :: List.foldr pushDef env typeDefs
                          end
                val domain = case domain
                             of SOME domain => domain
                              | NONE => FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
                do paramType := SOME (FlexFAst.OutputType (Concr domain))
                val codomain = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
                val body = elaborateExprAs env (Concr codomain) body
                val t = FType.Arrow (pos, {domain, codomain})
                val f = FTerm.Fn (pos, {var = param, typ = domain}, body)
            in ( List.foldr (fn (def, t) => FType.ForAll (pos, def, t)) t typeDefs
               , List.foldr (fn (def, f) => FTerm.TFn (pos, def, f)) f typeDefs)
            end*)
            raise Fail "unimplemented"
         | CTerm.Let (pos, stmts, body) =>
            let val env = Env.pushScope env (stmtsScope stmts)
                val stmts = Vector.map (elaborateStmt env) stmts
                val (typ, body) = elaborateExpr env body
            in (typ, FTerm.Let (pos, stmts, body))
            end
         | CTerm.If (pos, _, _, _) =>
            let val t = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
            in (t, elaborateExprAs env (Concr t) expr)
            end
         | CTerm.Record (pos, fields) => elaborateRecord env pos fields
         | CTerm.App (pos, {callee, arg}) =>
            let val ct as (_, callee) = elaborateExpr env callee
                val (callee, {domain, codomain}) = coerceCallee env ct 
                val arg = elaborateExprAs env (Concr domain) arg
            in (codomain, FTerm.App (pos, codomain, {callee, arg}))
            end
         | CTerm.Field (pos, expr, label) =>
            let val te as (_, expr) = elaborateExpr env expr
                val fieldType = coerceRecord env te label
            in (fieldType, FTerm.Field (pos, fieldType, expr, label))
            end
         | CTerm.Ann (pos, expr, t) =>
            let val dt as (_, t) = elaborateType env t
            in (t, elaborateExprAs env (FType.exist pos dt) expr)
            end
         | CTerm.Type (pos, t) =>
            let val t = FType.exist pos (elaborateType env t)
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
    and elaborateExprAs (env: Env.t) (typ: FlexFAst.Type.abs) (expr: CTerm.expr): FlexFAst.Type.sv FTerm.expr =
        case expr
        of CTerm.Fn (_, param, paramType, body) =>
            (case typ
             of Concr (FType.Arrow (_, {domain, codomain})) => raise Fail "unimplemented"
              | _ => coerceExprTo env typ expr)
         | CTerm.If (pos, cond, conseq, alt) =>
            FTerm.If (pos, elaborateExprAs env (Concr (FType.Prim (pos, FType.Prim.Bool))) cond
                         , elaborateExprAs env typ conseq
                         , elaborateExprAs env typ alt )
         | _ =>
           (case typ
            of Concr (FType.ForAll _) => raise Fail "unimplemented"
             | _ => coerceExprTo env typ expr)

    (* Like `elaborateExprAs`, but will always just do subtyping and apply the coercion. *)
    and coerceExprTo (env: Env.t) (typ: FlexFAst.Type.abs) (expr: CTerm.expr): FlexFAst.Type.sv FTerm.expr =
        let val (t', fexpr) = elaborateExpr env expr
            val coercion = subType env (CTerm.exprPos expr) (Concr t', typ)
        in applyCoercion coercion fexpr
        end

    (* Elaborate a statement and return the elaborated version. *)
    and elaborateStmt env: Cst.Term.stmt -> FlexFAst.Type.sv FTerm.stmt =
        fn CTerm.Val (pos, name, _, expr) =>
            let val (t, expr) =
                    case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                    of Unvisited (args as (_, SOME expr)) =>
                        let val t = unvisitedBindingType pos env name args
                        in (t, elaborateExprAs env (Concr t) expr)
                        end
                     | Visiting (args as (_, SOME expr)) =>
                        let val t = cyclicBindingType pos env name args
                        in (t, elaborateExprAs env (Concr t) expr)
                        end
                     | Typed (t, SOME expr) => (t, elaborateExprAs env (Concr t) expr)
                     | Visited (t, SOME expr) => (t, expr)
            in FTerm.Val (pos, {var = name, typ = t}, expr)
            end
         | CTerm.Expr expr => FTerm.Expr (elaborateExprAs env (Concr (FType.unit (CTerm.exprPos expr))) expr)

    (* Coerce `callee` into a function and return t coerced and its `domain` and `codomain`. *)
    and coerceCallee (env: Env.t) (typ: FlexFAst.Type.concr, callee: FlexFAst.Term.expr)
      : FlexFAst.Term.expr * {domain: FlexFAst.Type.concr, codomain: FlexFAst.Type.concr} =
        let fun coerce callee =
                fn FType.ForAll (_, {var, kind}, t) =>
                    let val pos = FTerm.exprPos callee
                        val uv = FType.SVar (pos, FlexFAst.Type.UVar (Env.newUv env (Predicative, Name.fromId var)))
                        val calleeType = FlexFAst.Type.Concr.substitute (var, uv) t
                    in coerce (FTerm.TApp (pos, calleeType, {callee, arg = uv})) calleeType
                    end
                 | FType.Arrow (_, domains) => (callee, domains)
                 | FType.SVar (_, FlexFAst.Type.UVar uv) =>
                    (case TypeVars.uvGet uv
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
                    (case TypeVars.uvGet uv
                     of Either.Right typ => coerce typ
                      | Either.Left uv => let val fieldType = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
                                              val ext = FType.SVar (pos, FlexFAst.Type.UVar (Env.freshUv env Predicative))
                                              val pos = FTerm.exprPos expr
                                              val row = FType.RowExt (pos, {field = (label, fieldType), ext})
                                              val typ = FType.Record (pos, row)
                                          in TypeVars.uvSet (uv, typ)
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
end

