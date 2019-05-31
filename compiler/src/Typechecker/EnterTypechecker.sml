structure EnterTypechecker :> sig
    val toTypechecking: FixedCst.Term.fexpr -> TypecheckingCst.expr * TypecheckingCst.expr_scope
end = struct
    structure CTerm = FixedCst.Term
    structure CType = FixedCst.Type
    structure TC = TypecheckingCst

    fun typeScope typ =
        fn _ => NONE

    fun stmtBind vals =
        fn CTerm.Val (_, name, typ, expr) =>
            let val binding = { shade = ref TC.White
                              , binder = {value = SOME expr, typ} }
            in NameHashTable.insert vals (name, binding)
            end
         | CTerm.Expr _ => ()

    fun exprScope expr =
        fn CTerm.Fn (_, arg, domain, _) =>
            let val binding = { shade = ref TC.White
                              , binder = {value = NONE, typ = domain} }
            in SOME {scope = TC.Scope.forFn (arg, binding), expr}
            end
         | CTerm.Let (_, stmts, _) =>
            let val vals = NameHashTable.mkTable (0, Subscript)
                do Vector.app (stmtBind vals) stmts
            in SOME {scope = TC.Scope.forBlock vals, expr}
            end
         | _ => NONE

    fun injectType (CType.FixT typ): TC.typ =
        let val typ = case typ
                      of CType.Arrow (pos, {domain, codomain}) =>
                          CType.Arrow (pos, { domain = injectType domain
                                            , codomain = injectType codomain })
                       | CType.Record (pos, row) => CType.Record (pos, injectType row)
                       | CType.RowExt (pos, {fields, ext}) =>
                          CType.RowExt (pos, { fields = Vector.map (Pair.second injectType) fields
                                             , ext = injectType ext })
                       | CType.EmptyRow pos => CType.EmptyRow pos
                       | CType.Path expr => CType.Path (injectExpr expr)
                       | CType.Type pos => CType.Type pos
                       | CType.Prim (pos, p) => CType.Prim (pos, p)
            val typ = TC.InputType typ
        in case typeScope typ typ
           of SOME scope => TC.ScopeType scope
            | NONE => typ
        end

    and injectExpr (CTerm.Fix expr): TC.expr =
        let val expr = case expr
                       of CTerm.Fn (pos, arg, odomain, body) =>
                           CTerm.Fn (pos, arg, ref (Option.map injectType odomain), injectExpr body)
                        | CTerm.Let (pos, stmts, body) =>
                           CTerm.Let (pos, Vector.map injectStmt stmts, injectExpr body)
                        | CTerm.Record (pos, row) => CTerm.Record (pos, injectRow row)
                        | CTerm.App (pos, {callee, arg}) =>
                           CTerm.App (pos, {callee = injectExpr callee, arg = injectExpr arg})
                        | CTerm.Field (pos, expr, label) => CTerm.Field (pos, injectExpr expr, label)
                        | CTerm.Ann (pos, expr, t) =>
                           CTerm.Ann (pos, injectExpr expr, injectType t)
                        | CTerm.Type (pos, t) => CTerm.Type (pos, injectType t)
                        | CTerm.Use (pos, name) => CTerm.Use (pos, name)
                        | CTerm.Const (pos, c) => CTerm.Const (pos, c)
            val iexpr = TC.InputExpr expr
        in case exprScope iexpr expr
           of SOME scope => TC.ScopeExpr scope
            | NONE => iexpr
        end

    and injectRow {fields, ext} = { fields = Vector.map (fn (label, expr) => (label, injectExpr expr)) fields
                                  , ext = Option.map injectExpr ext }

    and injectStmt (CTerm.Val (pos, name, otyp, expr)) =
        CTerm.Val (pos, name, ref (Option.map injectType otyp), ref (injectExpr expr))
      | injectStmt (CTerm.Expr expr) = CTerm.Expr (injectExpr expr)

    fun toTypechecking expr =
        let val expr = injectExpr expr
            val scope = case expr 
                        of TC.ScopeExpr {scope, expr = _} => scope
                         | _ => raise Fail "unreachable"
        in (expr, scope)
        end
end

