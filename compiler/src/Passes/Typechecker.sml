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
    val elaborateExpr: TypecheckingCst.scope -> TypecheckingCst.expr ref -> TypecheckingCst.typ ref
   
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

    fun subType (typRef, superTypRef) =
        case (!typRef, !superTypRef)
        of (TC.OutputType (FType.Prim (_, pl)), TC.OutputType (FType.Prim (_, pr))) =>
            if pl = pr
            then NONE
            else raise Fail "<:"

    local
        fun unfixExpr exprRef =
            case !exprRef
            of TC.OutputExpr expr => expr
             | TC.ScopeExpr {expr, ...} => unfixExpr expr
             | TC.InputExpr _ => raise Fail "unfix encountered InputExpr"
    in
        val fExprType = FTerm.typeOf (ref o TC.OutputType) unfixExpr
    end

    fun valShadeRef name =
        fn TC.ExprScope {vals, parent, ...} =>
            (case NameHashTable.find vals name
             of SOME {shade, ...} => shade
              | NONE =>
                 (case Option.map (valShadeRef name) (!parent)
                  of SOME shade => shade
                   | NONE => raise Fail ("valShadeRef: unbound " ^ Name.toString name)))

    fun lookupType name scope =
        case scope
        of TC.ExprScope {vals, parent, ...} =>
            (case NameHashTable.find vals name
             of SOME {shade, binder} =>
                 (case !shade
                  of TC.Black => SOME (#typ binder)
                   | TC.White => SOME (elaborateType scope name (#typ binder))
                   | TC.Grey =>
                      raise Fail ("lookupType cycle at " ^ Name.toString name))
              | NONE => Option.mapPartial (lookupType name) (!parent))

    and elaborateType scope name typRef =
        case !typRef
        of TC.InputType typ =>
            let do valShadeRef name scope := TC.Grey
                val typ = case typ
                          of CType.Prim (pos, p) => FType.Prim (pos, p)
            in typRef := TC.OutputType typ
             ; valShadeRef name scope := TC.Black
             ; typRef
            end
         | TC.ScopeType (scope as {typ, ...}) => elaborateType (TC.TypeScope scope) name typ
         | TC.OutputType _ | TC.OVar _ | TC.UVar _ => typRef

    fun elaborateExpr scope exprRef =
        case !exprRef
        of TC.InputExpr expr =>
            (case expr
             of CTerm.Let (pos, stmts, body) =>
                 let val stmts = Vector.map (elaborateStmt scope) stmts
                     val typ = elaborateExpr scope body
                 in exprRef := TC.OutputExpr (FTerm.Let (pos, stmts, body))
                  ; typ
                 end
              | CTerm.App (pos, {callee, arg}) =>
                 let val {domain, codomain} = coerceCallee callee (elaborateExpr scope callee)
                 in elaborateExprAs scope domain arg
                  ; exprRef := TC.OutputExpr (FTerm.App (pos, codomain, {callee, arg}))
                  ; codomain
                 end
              | CTerm.Ann (pos, expr, t) =>
                 ( elaborateExprAs scope t expr
                 ; t )
              | CTerm.Use (pos, name) =>
                 let val typRef = case lookupType name scope
                                  of SOME typRef => typRef
                                   | NONE => raise Fail ("unbound variable: " ^ Name.toString name)
                     val def = { var = name, typ = typRef }
                 in exprRef := TC.OutputExpr (FTerm.Use (pos, def))
                  ; typRef
                 end
              | CTerm.Const (pos, c) =>
                 ( exprRef := TC.OutputExpr (FTerm.Const (pos, c))
                 ; ref (TC.OutputType (FType.Prim (pos, Const.typeOf c))) ))
         | TC.ScopeExpr (scope as {expr, ...}) => elaborateExpr (TC.ExprScope scope) expr
         | TC.OutputExpr expr =>
            (* Assumes invariant: the whole subtree has been elaborated already. *)
            fExprType expr

    and elaborateExprAs scope typRef exprRef =
        case (!typRef, !exprRef)
        of (TC.InputType t, TC.InputExpr expr) =>
            (case (t, expr)
             of (FType.ForAll _, expr) => raise Fail "unimplemented"
              | (FType.Arrow _, CTerm.Fn _) => raise Fail "unimplemented"
              | (_, _) =>
                 let val t' = elaborateExpr scope exprRef
                     val coercion = getOpt (subType (t', typRef), ignore)
                 in coercion exprRef
                 end)
         | (_, TC.ScopeExpr (scope as {expr, ...})) => ignore (elaborateExpr (TC.ExprScope scope) expr)
         | (_, TC.OutputExpr expr) =>
            (* Assumes invariant: the whole subtree has been elaborated already. *)
            ignore (fExprType expr)

    and elaborateStmt scope =
        fn CTerm.Val (pos, name, SOME annTypeRef, exprRef) =>
            let val exprType = elaborateExpr scope exprRef
                val annType = elaborateType scope name annTypeRef
                val coercion = getOpt (subType (exprType, annType), ignore)
            in coercion exprRef
             ; FTerm.Val (pos, {var = name, typ = annTypeRef}, exprRef)
            end
         | CTerm.Expr exprRef =>
            ( ignore (elaborateExpr scope exprRef)
            ; FTerm.Expr exprRef )

    and coerceCallee callee typRef =
        case !typRef
        of TC.InputType _ => raise Fail "unimplemented"
         | TC.ScopeType (scope as {typ, ...}) => raise Fail "unimplemented"
         | TC.OutputType typ =>
            (case typ
             of FType.ForAll _ => raise Fail "unimplemented"
              | FType.Arrow (_, domains) => domains
              | _ => raise Fail "uncallable")
         | TC.OVar _ => raise Fail "uncallable"
         | TC.UVar uv =>
            (case TypeVars.uvGet uv
             of Either.Left uv => raise Fail "uniplemented"
              | Either.Right typ => coerceCallee callee typ)
end

