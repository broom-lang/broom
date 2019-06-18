structure EnterTypechecker :> sig
    val toTypechecking: FixedCst.Term.fexpr -> TypecheckingCst.expr * TypecheckingCst.expr_scope
end = struct
    structure CTerm = Cst.Term
    structure CType = Cst.Type
    structure TC = TypecheckingCst

    fun declBind types (name, typ) =
        let val binding = { shade = ref TC.White
                          , binder = {value = NONE, typ} }
        in NameHashTable.insert types (name, binding)
        end

    fun typeScope (typ: TC.typ): (TC.typ, TC.typ option ref, TC.expr) CType.typ -> {scope: TC.expr_scope, typ: TC.typ} option =
        fn CType.Pi (_, {var, typ = domain}, _) =>
            let val binding = { shade = ref TC.White
                              , binder = {value = NONE, typ = domain} }
            in SOME {scope = TC.Scope.forFn (var, binding), typ}
            end
         | CType.Interface (_, decls) =>
            let val types = NameHashTable.mkTable (0, Subscript)
                do Vector.app (declBind types) decls
            in SOME {scope = TC.Scope.forBlock types, typ}
            end
         | _ => NONE

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
         | CTerm.Let (_, stmts, _) | CTerm.Module (_, stmts) =>
            let val vals = NameHashTable.mkTable (0, Subscript)
                do Vector.app (stmtBind vals) stmts
            in SOME {scope = TC.Scope.forBlock vals, expr}
            end
         | _ => NONE

    fun injectType (CType.FixT typ): TC.typ =
        let val typ = case typ
                      of CType.Pi (pos, {var, typ = domain}, codomain) =>
                          CType.Pi (pos, {var, typ = ref (Option.map injectType domain)}, injectType codomain)
                       | CType.Record (pos, row) => CType.Record (pos, injectType row)
                       | CType.RowExt (pos, {fields, ext}) =>
                          CType.RowExt (pos, { fields = Vector.map (Pair.second injectType) fields
                                             , ext = injectType ext })
                       | CType.EmptyRow pos => CType.EmptyRow pos
                       | CType.WildRow pos => CType.WildRow pos
                       | CType.Interface (pos, decls) =>
                          CType.Interface (pos, Vector.map (Pair.second (ref o Option.map injectType)) decls)
                       | CType.Path expr => CType.Path (injectExpr expr)
                       | CType.Singleton (pos, expr) => CType.Singleton (pos, injectExpr expr)
                       | CType.Type pos => CType.Type pos
                       | CType.Prim (pos, p) => CType.Prim (pos, p)
            val ityp = TC.InputType typ
        in case typeScope ityp typ
           of SOME scope => TC.ScopeType scope
            | NONE => ityp
        end

    and injectExpr (CTerm.Fix expr): TC.expr =
        let val expr = case expr
                       of CTerm.Fn (pos, arg, odomain, body) =>
                           CTerm.Fn (pos, arg, ref (Option.map injectType odomain), injectExpr body)
                        | CTerm.Let (pos, stmts, body) =>
                           CTerm.Let (pos, Vector.map injectStmt stmts, injectExpr body)
                        | CTerm.If (pos, cond, conseq, alt) =>
                           CTerm.If (pos, injectExpr cond, injectExpr conseq, injectExpr alt)
                        | CTerm.Record (pos, row) => CTerm.Record (pos, injectRow row)
                        | CTerm.Module (pos, stmts) =>
                           CTerm.Module (pos, Vector.map injectStmt stmts)
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

