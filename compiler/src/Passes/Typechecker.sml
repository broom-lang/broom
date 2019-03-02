structure Typechecker :> sig
    val injectType: FixedCst.Type.typ -> TypecheckingCst.typ ref
    val injectExpr: FixedCst.Term.expr -> TypecheckingCst.expr ref
    (* TODO: Link scope parents *)
    (* TODO: Actual type checking *)
    (* TODO: Finishing elaboration ('ejection'?) *)
end = struct
    structure CTerm = FixedCst.Term
    structure CType = FixedCst.Type
    structure TC = TypecheckingCst

    fun typeScope typ =
        fn CType.ForAll (pos, def as {var, kind}, _) =>
            let val types = NameHashTable.mkTable (1, Subscript)
                val binding = {kind, typ = SOME (ref (TC.InputType (CType.UseT (pos, def))))}
                do NameHashTable.insert types (var, binding)
            in SOME {parent = ref NONE, typ, types}
            end
         | _ => NONE

    fun stmtBind vals =
        fn CTerm.Val (_, name, SOME typ, expr) =>
            let val binding = {value = SOME expr, typ}
            in NameHashTable.insert vals (name, binding)
            end
         | CTerm.Expr expr => ()

    fun exprScope expr =
        fn CTerm.Fn (_, arg, SOME domain, _) =>
            let val vals = NameHashTable.mkTable (1, Subscript)
                val binding = {value = NONE, typ = domain}
                do NameHashTable.insert vals (arg, binding)
            in SOME {parent = ref NONE, expr, vals}
            end
         | CTerm.Let (_, stmts, _) =>
            let val vals = NameHashTable.mkTable (0, Subscript)
                do Vector.app (stmtBind vals) stmts
            in SOME {parent = ref NONE, expr, vals}
            end
         | _ => NONE

    fun injectType (CType.Fix typ) =
        let val typ = case typ
                      of CType.ForAll (pos, def, body) =>
                          CType.ForAll (pos, def, injectType body)
                       | CType.Arrow (pos, {domain, codomain}) =>
                          CType.Arrow (pos, { domain = injectType domain
                                            , codomain = injectType codomain })
                       | CType.UseT (pos, def) => CType.UseT (pos, def)
                       | CType.Prim (pos, p) => CType.Prim (pos, p)
            val flexType = ref (TC.InputType typ)
        in case typeScope flexType typ
           of SOME scope => ref (TC.ScopeType scope)
            | NONE => flexType
        end

    fun injectExpr (CTerm.Fix expr) =
        let val expr = case expr
                       of CTerm.Fn (pos, arg, SOME domain, body) =>
                           CTerm.Fn (pos, arg, SOME (injectType domain), injectExpr body)
                        | CTerm.Let (pos, stmts, body) =>
                           CTerm.Let (pos, Vector.map injectStmt stmts, injectExpr body)
                        | CTerm.App (pos, {callee, arg}) =>
                           CTerm.App (pos, { callee = injectExpr callee
                                           , arg = injectExpr arg })
                        | CTerm.Ann (pos, expr, t) =>
                           CTerm.Ann (pos, injectExpr expr, injectType t)
                        | CTerm.Use (pos, name) => CTerm.Use (pos, name)
                        | CTerm.Const (pos, c) => CTerm.Const (pos, c)
            val flexpr = ref (TC.InputExpr expr)
        in case exprScope flexpr expr
           of SOME scope => ref (TC.ScopeExpr scope)
            | NONE => flexpr
        end
    
    and injectStmt (CTerm.Val (pos, name, otyp, expr)) =
        CTerm.Val (pos, name, Option.map injectType otyp, injectExpr expr)
      | injectStmt (CTerm.Expr expr) = CTerm.Expr (injectExpr expr)
end

