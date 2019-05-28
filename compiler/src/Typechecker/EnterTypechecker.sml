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
            let val vals = NameHashTable.mkTable (1, Subscript)
                val binding = { shade = ref TC.White
                              , binder = {value = NONE, typ = domain} }
                do NameHashTable.insert vals (arg, binding)
            in SOME {parent = ref NONE, expr, vals}
            end
         | CTerm.Let (_, stmts, _) =>
            let val vals = NameHashTable.mkTable (0, Subscript)
                do Vector.app (stmtBind vals) stmts
            in SOME {parent = ref NONE, expr, vals}
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

(***)

    fun uplinkTypeScopes parentScope =
        fn TC.ScopeType (scope as {parent, typ, ...}) =>
            ( parent := parentScope
            ; uplinkTypeScopes (SOME (TC.TypeScope scope)) typ )
         | TC.InputType typ =>
            (case typ
             of CType.Arrow (_, {domain, codomain}) =>
                 ( uplinkTypeScopes parentScope domain
                 ; uplinkTypeScopes parentScope codomain )
              | _ => ())
         | TC.OutputType _ => raise Fail "uplinkTypeScopes encountered an OutputType"
         | TC.OVar _ | TC.UVar _ => ()

    fun uplinkExprScopes parentScope =
        fn TC.ScopeExpr (scope as {parent, expr, ...}) =>
            ( parent := parentScope
            ; uplinkExprScopes (SOME (TC.ExprScope scope)) expr )
         | TC.InputExpr expr =>
            (case expr
             of CTerm.Fn (_, _, domain, body) =>
                 ( Option.app (uplinkTypeScopes parentScope) (!domain)
                 ; uplinkExprScopes parentScope body )
              | CTerm.Let (_, stmts, body) =>
                 ( Vector.app (uplinkStmtScopes parentScope) stmts
                 ; uplinkExprScopes parentScope body )
              | CTerm.Record (_, {fields, ext}) =>
                 ( Vector.app (uplinkExprScopes parentScope o #2) fields
                 ; Option.app (uplinkExprScopes parentScope) ext )
              | CTerm.App (_, {callee, arg}) =>
                 ( uplinkExprScopes parentScope callee
                 ; uplinkExprScopes parentScope arg )
              | CTerm.Field (_, expr, _) => uplinkExprScopes parentScope expr
              | CTerm.Ann (_, expr, t) =>
                 ( uplinkExprScopes parentScope expr
                 ; uplinkTypeScopes parentScope t )
              | CTerm.Type (_, typ) => uplinkTypeScopes parentScope typ
              | CTerm.Use _ | CTerm.Const _ => ())
         | TC.OutputExpr _ => raise Fail "uplinkExprScopes encountered an OutputExpr"

    and uplinkStmtScopes parentScope =
        fn CTerm.Val (_, _, typ, expr) =>
            ( Option.app (uplinkTypeScopes parentScope) (!typ)
            ; uplinkExprScopes parentScope (!expr) )
         | CTerm.Expr expr => uplinkExprScopes parentScope expr

    fun toTypechecking expr =
        let val expr = injectExpr expr
            do uplinkExprScopes NONE expr
            val scope = case expr 
                        of TC.ScopeExpr scope => scope
                         | _ => raise Fail "unreachable"
        in (expr, scope)
        end
end

