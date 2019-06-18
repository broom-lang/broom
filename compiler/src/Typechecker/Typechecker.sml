structure Typechecker :> sig
    val elaborateExpr: TypecheckingEnv.t -> Cst.Term.expr
                     -> TypecheckingCst.concr * TypecheckingCst.sv FAst.Term.expr
end = struct
    datatype predicativity = datatype TypeVars.predicativity
    structure CTerm = Cst.Term
    structure CType = Cst.Type
    structure TC = TypecheckingCst
    structure FTerm = FAst.Term
    structure FType = FAst.Type
    datatype abs = datatype FType.abs

    open TypeError

    structure Env = TypecheckingEnv
    datatype expr_binding_state = datatype Env.Bindings.Expr.binding_state
 
    val subType = Subtyping.subType
    val applyCoercion = Subtyping.applyCoercion

(* Looking up `val` types *)
    fun unvisitedBindingType expr env name args =
        let val pos = CTerm.exprPos expr
            do Env.updateExpr pos env name (Fn.constantly (Visiting args))
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
                    let val t = FType.SVar (pos, TC.UVar (Env.freshUv env Predicative))
                    in (t, Typed (t, oexpr))
                    end
        in case valOf (Env.findExpr env name)
           of Unvisited _ => raise Fail "unreachable"
            | Visiting _ =>
               ( Env.updateExpr pos env name (Fn.constantly binding')
                ; t )
            | Typed (usageTyp, _) | Visited (usageTyp, _) =>
               ( ignore (subType env expr (Concr t, Concr usageTyp))
               ; usageTyp )
        end
       
    and cyclicBindingType pos env name (_, oexpr) =
        let val t = FType.SVar (pos, TC.UVar (Env.freshUv env Predicative))
        in Env.updateExpr pos env name (Fn.constantly (Typed (t, oexpr)))
         ; t
        end

    (* Get the type of the variable `name`, referenced at `pos`, from `env` by either
       - finding the type annotation (if available) (and elaborating it if not already done)
       - elaborating the expression bound to the variable (if available)
       - returning a fresh unification variable (if neither type annotation nor bound expression
         is available or if a cycle is encountered) *)
    and lookupValType expr name env: TC.concr option =
        Option.map (fn (Unvisited args, env) => unvisitedBindingType expr env name args
                     | (Visiting args, env) => cyclicBindingType (CTerm.exprPos expr) env name args
                     | (Typed (t, _) | Visited (t, _), _) => t)
                   (Env.findExprClosure env name)

(* Elaborating subtrees *)

    (* FIXME: Actually need a mutable 'exists' scope where we put the defs,
              kind of like how sealing puts its generated types in the toplevel scope.
              The current scheme does not even support non-cyclic forward references. *)
    (*and elaborateType (env: Env.t): TC.typ -> FType.def list * TC.concr =
        fn TC.InputType typ =>
            (case typ
             of CType.Pi (pos, {var, typ = paramType}, codomain) =>
                 let val (ddefs as [], domain) = case !paramType
                                                 of SOME domain => elaborateType env domain
                                                  | NONE => raise Fail "unimplemented"
                     do paramType := SOME (TC.OutputType (Concr domain))
                     val (cddefs as [], codomain) = elaborateType env codomain
                 in (cddefs @ cddefs, FType.Arrow (pos, {domain, codomain}))
                 end
              | CType.Record (pos, row) =>
                 let val (defs, row) = elaborateType env row
                 in (defs, FType.Record (pos, row))
                 end
              | CType.RowExt (pos, {fields, ext}) =>
                 let fun elaborateField ((label, t), (defs, fields)) =
                         let val (defs', t) = elaborateType env t
                         in (defs @ defs', (label, t) :: fields)
                         end
                     fun constructStep (field, ext) = FType.RowExt (pos, {field, ext})
                     val (fieldDefs, revFields) = Vector.foldl elaborateField ([], []) fields
                     val (extDefs, ext) = elaborateType env ext
                 in (fieldDefs @ extDefs, List.foldl constructStep ext revFields)
                 end
              | CType.EmptyRow pos => ([], FType.EmptyRow pos)
              | CType.WildRow pos =>
                 let val def = {var = Id.fresh (), kind = FType.RowK pos}
                 in ([def], FType.UseT (pos, def))
                 end
              | CType.Interface (pos, decls) =>
                 let fun step ((name, t), (defs, fields)) =
                         let val (defs', dt) = case !t
                                               of SOME t => elaborateType env t
                                                | NONE => raise Fail "unimplemented"
                             do t := SOME (TC.OutputType (Concr dt))
                         in (defs @ defs', (name, dt) :: fields)
                         end
                     val (defs, revFields) = Vector.foldl step ([], []) decls
                     fun constructStep (field, ext) = FType.RowExt (pos, {field, ext})
                 in (defs, FType.Record (pos, List.foldr constructStep (FType.EmptyRow pos) revFields))
                 end
              | CType.Path typExpr =>
                 let val (typ, _) = elaborateExpr env typExpr
                 in case typ
                    of FType.Type (_, typ) => FType.splitExistentials typ
                     | _ => raise Fail ("Type path " ^ TC.Type.concrToString typ
                                        ^ "does not denote type at " ^ Pos.toString (TC.Expr.pos typExpr))
                 end
              | CType.Type pos =>
                 let val def = {var = Id.fresh (), kind = FType.TypeK pos}
                 in ([def], FType.Type (pos, Concr (FType.UseT (pos, def))))
                 end
              | CType.Prim (pos, p) => ([], FType.Prim (pos, p)))
         | TC.OutputType t => FType.splitExistentials t (* assumes invariant: entire subtree has been elaborated already *)*)

    (* Elaborate the type `typ` and return the elaborated version. *)
    and elaborateType (env: Env.t) (t: CType.typ): FType.def list * TC.concr =
        let val absBindings = Env.Bindings.Type.new ()
            val absScope = Env.Scope.ExistsScope (Env.Scope.Id.fresh (), absBindings)
            val env = Env.pushScope env absScope
            val rec elaborate =
                fn CType.Prim (pos, p) => FType.Prim (pos, p)
            val t = elaborate t
            val defs = Env.Bindings.Type.defs absBindings
        in (defs, t)
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
    and elaborateExpr (env: Env.t) (expr: CTerm.expr): TC.concr * TC.sv FTerm.expr =
        case expr
        of CTerm.Fn (pos, param, paramType, body) =>
            (*let val (typeDefs, domain) =
                    case !paramType
                    of SOME domain => Pair.second SOME (elaborateType env domain)
                     | NONE => ([], NONE)
                val env = let val fnScope :: env = env
                              fun pushDef ({var, kind}, env) =
                                  let val bindingRef = ref NONE
                                      val scope = TC.TypeScope (TC.Scope.forTFn (var, bindingRef))
                                      val env = scope :: env
                                  in bindingRef := SOME {binder = kind, shade = ref TC.Black}
                                   ; env
                                  end
                          in fnScope :: List.foldr pushDef env typeDefs
                          end
                val domain = case domain
                             of SOME domain => domain
                              | NONE => FType.SVar (pos, TC.UVar (Env.freshUv env Predicative))
                do paramType := SOME (TC.OutputType (Concr domain))
                val codomain = FType.SVar (pos, TC.UVar (Env.freshUv env Predicative))
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
            let val t = FType.SVar (pos, TC.UVar (Env.freshUv env Predicative))
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

    and elaborateRecord env pos ({fields, ext}: CTerm.row): TC.concr * TC.sv FTerm.expr =
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
    and elaborateExprAs (env: Env.t) (typ: TC.abs) (expr: CTerm.expr): TC.sv FTerm.expr =
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
    and coerceExprTo (env: Env.t) (typ: TC.abs) (expr: CTerm.expr): TC.sv FTerm.expr =
        let val (t', fexpr) = elaborateExpr env expr
            val coercion = subType env expr (Concr t', typ)
        in applyCoercion coercion fexpr
        end

    (* Elaborate a statement and return the elaborated version. *)
    and elaborateStmt env: Cst.Term.stmt -> TC.sv FTerm.stmt =
        fn CTerm.Val (pos, name, _, expr) =>
            let val (t, expr) =
                    case valOf (Env.findExpr env name) (* `name` is in `env` by construction *)
                    of Unvisited (args as (_, SOME expr)) =>
                        let val t = unvisitedBindingType expr env name args
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
    and coerceCallee (env: Env.t) (typ: TC.concr, callee: TC.sv FTerm.expr): TC.sv FTerm.expr * {domain: TC.concr, codomain: TC.concr} =
        let fun coerce callee =
                fn FType.ForAll (_, {var, kind}, t) =>
                    let val pos = FTerm.exprPos callee
                        val uv = FType.SVar (pos, TC.UVar (Env.newUv env (Predicative, Name.fromId var)))
                        val calleeType = TC.Type.substitute (var, uv) t
                    in coerce (FTerm.TApp (pos, calleeType, {callee, arg = uv})) calleeType
                    end
                 | FType.Arrow (_, domains) => (callee, domains)
                 | FType.SVar (_, TC.UVar uv) =>
                    (case TypeVars.uvGet uv
                     of Either.Left uv => raise Fail "unimplemented"
                      | Either.Right typ => coerce callee typ)
                 | _ => raise TypeError (UnCallable (callee, typ))
        in coerce callee typ
        end
   
    (* Coerce `expr` (in place) into a record with at least `label` and return the `label`:ed type. *)
    and coerceRecord env (typ: TC.concr, expr: TC.sv FTerm.expr) label: TC.concr =
        let val rec coerce =
                fn FType.ForAll _ => raise Fail "unimplemented"
                 | FType.Record (_, row) => coerceRow row
                 | FType.SVar (pos, TC.UVar uv) =>
                    (case TypeVars.uvGet uv
                     of Either.Right typ => coerce typ
                      | Either.Left uv => let val fieldType = FType.SVar (pos, TC.UVar (Env.freshUv env Predicative))
                                              val ext = FType.SVar (pos, TC.UVar (Env.freshUv env Predicative))
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

