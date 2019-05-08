structure EnterTypechecker :> sig
    val toTypechecking: FixedCst.Term.expr -> TypecheckingCst.expr ref * TypecheckingCst.expr_scope
end = struct
    structure CTerm = FixedCst.Term
    structure CType = FixedCst.Type
    structure TC = TypecheckingCst

    fun typeScope typ =
        fn _ => NONE

    fun stmtBind vals =
        fn CTerm.Val (_, name, otyp, expr) =>
            let val binding = { shade = ref TC.White
                              , binder = {value = SOME expr, typ = ref (Option.map op! otyp)} }
            in NameHashTable.insert vals (name, binding)
            end
         | CTerm.Expr _ => ()

    fun exprScope expr =
        fn CTerm.Fn (_, arg, odomain, _) =>
            let val vals = NameHashTable.mkTable (1, Subscript)
                val binding = { shade = ref TC.White
                              , binder = {value = NONE, typ = ref (Option.map op! odomain)} }
                do NameHashTable.insert vals (arg, binding)
            in SOME {parent = ref NONE, expr, vals}
            end
         | CTerm.Let (_, stmts, _) =>
            let val vals = NameHashTable.mkTable (0, Subscript)
                do Vector.app (stmtBind vals) stmts
            in SOME {parent = ref NONE, expr, vals}
            end
         | _ => NONE

    fun injectType (CType.FixT typ) =
        let val typ = case typ
                      of CType.Arrow (pos, {domain, codomain}) =>
                          CType.Arrow (pos, { domain = injectType domain
                                            , codomain = injectType codomain })
                       | CType.Path expr => CType.Path (injectExpr expr)
                       | CType.Prim (pos, p) => CType.Prim (pos, p)
            val flexType = ref (TC.InputType typ)
        in case typeScope flexType typ
           of SOME scope => ref (TC.ScopeType scope)
            | NONE => flexType
        end

    and injectExpr (CTerm.Fix expr) =
        let val expr = case expr
                       of CTerm.Fn (pos, arg, odomain, body) =>
                           CTerm.Fn (pos, arg, Option.map injectType odomain, injectExpr body)
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
            val flexpr = ref (TC.InputExpr expr)
        in case exprScope flexpr expr
           of SOME scope => ref (TC.ScopeExpr scope)
            | NONE => flexpr
        end

    and injectRow row = Vector.map (fn (label, expr) => (label, injectExpr expr)) row

    and injectStmt (CTerm.Val (pos, name, otyp, expr)) =
        CTerm.Val (pos, name, Option.map injectType otyp, injectExpr expr)
      | injectStmt (CTerm.Expr expr) = CTerm.Expr (injectExpr expr)

(***)

    fun uplinkTypeScopes parentScope typRef =
        case !typRef
        of TC.ScopeType (scope as {parent, typ, ...}) =>
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

    fun uplinkExprScopes parentScope exprRef =
        case !exprRef
        of TC.ScopeExpr (scope as {parent, expr, ...}) =>
            ( parent := parentScope
            ; uplinkExprScopes (SOME (TC.ExprScope scope)) expr )
         | TC.InputExpr expr =>
            (case expr
             of CTerm.Fn (_, _, domain, body) =>
                 ( Option.app (uplinkTypeScopes parentScope) domain
                 ; uplinkExprScopes parentScope body )
              | CTerm.Let (_, stmts, body) =>
                 ( Vector.app (uplinkStmtScopes parentScope) stmts
                 ; uplinkExprScopes parentScope body )
              | CTerm.Record (_, row) => Vector.app (uplinkExprScopes parentScope o #2) row
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
            ( Option.app (uplinkTypeScopes parentScope) typ
            ; uplinkExprScopes parentScope expr )
         | CTerm.Expr expr => uplinkExprScopes parentScope expr

    fun toTypechecking expr =
        let val exprRef = injectExpr expr
            do uplinkExprScopes NONE exprRef
            val scope = case !exprRef
                        of TC.ScopeExpr scope => scope
                         | _ => raise Fail "unreachable"
        in (exprRef, scope)
        end
end

