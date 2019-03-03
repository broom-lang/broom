structure Typechecker :> sig
    val stmtBind: (TypecheckingCst.typ ref, TypecheckingCst.expr ref) TypecheckingCst.val_binding TypecheckingCst.bindings
                  -> (TypecheckingCst.typ ref, TypecheckingCst.expr ref) Cst.Term.stmt -> unit
    val injectType: FixedCst.Type.typ -> TypecheckingCst.typ ref
    val injectExpr: FixedCst.Term.expr -> TypecheckingCst.expr ref
    val injectStmt: FixedCst.Term.stmt
                    -> (TypecheckingCst.typ ref, TypecheckingCst.expr ref) Cst.Term.stmt

    val uplinkTypeScopes: TypecheckingCst.scope option -> TypecheckingCst.typ ref -> unit
    val uplinkExprScopes: TypecheckingCst.scope option -> TypecheckingCst.expr ref -> unit
    val uplinkStmtScopes: TypecheckingCst.scope option
                          -> (TypecheckingCst.typ ref, TypecheckingCst.expr ref) Cst.Term.stmt
                          -> unit
    
    (* TODO: Actual type checking *)
    val elaborateExpr: TypecheckingCst.scope -> TypecheckingCst.expr ref
                       -> TypecheckingCst.typ ref FAst.Type.typ
   
    (* TODO: Finishing elaboration ('ejection'?) *)
end = struct
    structure CTerm = FixedCst.Term
    structure CType = FixedCst.Type
    structure TC = TypecheckingCst
    structure FTerm = FAst.Term
    structure FType = FAst.Type

    fun typeScope typ =
        fn CType.ForAll (pos, def as {var, kind}, _) =>
            let val types = NameHashTable.mkTable (1, Subscript)
                val binding = { shade = ref TC.White
                              , binder = { kind
                                         , typ = SOME (ref (TC.InputType (CType.UseT (pos, def)))) } }
                do NameHashTable.insert types (var, binding)
            in SOME {parent = ref NONE, typ, types}
            end
         | _ => NONE

    fun stmtBind vals =
        fn CTerm.Val (_, name, SOME typ, expr) =>
            let val binding = {shade = ref TC.White, binder = {value = SOME expr, typ}}
            in NameHashTable.insert vals (name, binding)
            end
         | CTerm.Expr _ => ()

    fun exprScope expr =
        fn CTerm.Fn (_, arg, SOME domain, _) =>
            let val vals = NameHashTable.mkTable (1, Subscript)
                val binding = {shade = ref TC.White, binder = {value = NONE, typ = domain}}
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

(***)

    fun uplinkTypeScopes parentScope typRef =
        case !typRef
        of TC.ScopeType (scope as {parent, typ, ...}) =>
            ( parent := parentScope
            ; uplinkTypeScopes (SOME (TC.TypeScope scope)) typ )
         | TC.InputType typ =>
            (case typ
             of CType.ForAll (_, _, body) => uplinkTypeScopes parentScope body
              | CType.Arrow (_, {domain, codomain}) =>
                 ( uplinkTypeScopes parentScope domain
                 ; uplinkTypeScopes parentScope codomain )
              | _ => ())
         | TC.OutputType _ => raise Fail "uplinkTypeScopes encountered an OutputType"

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
              | CTerm.App (_, {callee, arg}) =>
                 ( uplinkExprScopes parentScope callee
                 ; uplinkExprScopes parentScope arg )
              | CTerm.Ann (_, expr, t) =>
                 ( uplinkExprScopes parentScope expr
                 ; uplinkTypeScopes parentScope t )
              | _ => ())
         | TC.OutputExpr _ => raise Fail "uplinkExprScopes encountered an OutputExpr"

    and uplinkStmtScopes parentScope =
        fn CTerm.Val (_, _, typ, expr) =>
            ( Option.app (uplinkTypeScopes parentScope) typ
            ; uplinkExprScopes parentScope expr )
         | CTerm.Expr expr => uplinkExprScopes parentScope expr

(***)

    local
        fun unfix exprRef =
            case !exprRef
            of TC.OutputExpr expr => expr
             | TC.ScopeExpr {expr, ...} => unfix expr
             | TC.InputExpr _ => raise Fail "unfix encountered InputExpr"
    in
        val fExprType = FTerm.typeOf (ref o TC.OutputType) unfix
    end

    fun lookupType name scope =
        case scope
        of TC.ExprScope {vals, parent, ...} =>
            (case NameHashTable.find vals name
             of SOME {shade, binder} =>
                 (case !shade
                  of TC.Black =>
                      (case !(#typ binder)
                       of TC.OutputType typ => SOME typ)
                   | TC.White => SOME (elaborateType scope name (#typ binder))
                   | TC.Grey =>
                      raise Fail ("lookupType cycle at " ^ Name.toString name))
              | NONE => Option.mapPartial (lookupType name) (!parent))

    and elaborateType scope name typRef =
        (* TODO: Setting shade first to grey, then black *)
        (* TODO: Setting typRef to an OutputType *)
        case !typRef
        of TC.InputType typ =>
            let val typ =
                case typ
                of CType.Prim (pos, p) => FType.Prim (pos, p)
            in typRef := TC.OutputType typ
             ; typ
            end

    fun elaborateExpr scope exprRef =
        case !exprRef
        of TC.InputExpr expr =>
            let val (expr, typ) =
                (case expr
                 of CTerm.Let (pos, stmts, body) =>
                     let val stmts = Vector.map (elaborateStmt scope) stmts
                         val typ = elaborateExpr scope body
                     in (FTerm.Let (pos, stmts, body), typ)
                     end
                  | CTerm.Use (pos, name) =>
                     let val typ = case lookupType name scope
                                   of SOME typ => typ
                                    | NONE => raise Fail ("unbound variable: " ^ Name.toString name)
                         val def = { var = name
                                   , typ = ref (TC.OutputType typ) } (* HACK: fresh ref *)
                     in (FTerm.Use (pos, def), typ)
                     end
                  | CTerm.Const (pos, c) => (FTerm.Const (pos, c), FType.Prim (pos, Const.typeOf c)))
            in exprRef := TC.OutputExpr expr
             ; typ
            end
         | TC.ScopeExpr (scope as {expr, ...}) => elaborateExpr (TC.ExprScope scope) expr
         | TC.OutputExpr expr =>
            (* Assumes invariant: the whole subtree has been elaborated already. *)
            (case !(fExprType expr)
             of TC.OutputType typ => typ)

    and elaborateStmt scope =
        fn CTerm.Val (pos, name, SOME annTypeRef, exprRef) =>
            let val exprType = elaborateExpr scope exprRef
                val annType = elaborateType scope name annTypeRef
            in if exprType = annType (* FIXME: Should be subtype check *)
               then FTerm.Val (pos, {var = name, typ = annTypeRef}, exprRef)
               else raise Fail "type mismatch"
            end
         | CTerm.Expr exprRef =>
            ( ignore (elaborateExpr scope exprRef)
            ; FTerm.Expr exprRef )
end

