structure ExitTypechecker :> sig
    val toF: TypecheckingCst.expr ref -> FixedFAst.Term.expr
end = struct
    structure Env :> sig
        type ('t, 'v) t

        val empty: ('t, 'v) t 
        val insertVal: ('t, 'v) t -> Name.t * 'v -> ('t, 'v) t
        val insertType: ('t, 'v) t -> Name.t * 't -> ('t, 'v) t
        val lookupVal: ('t, 'v) t * Name.t -> 'v
        val lookupType: ('t, 'v) t * Name.t -> 't
    end = struct
        type ('t, 'v) t = { types: 't NameSortedMap.map
                          , vals: 'v NameSortedMap.map }

        val empty = {types = NameSortedMap.empty, vals = NameSortedMap.empty}

        fun insertVal {types, vals} (k, v) = {types, vals = NameSortedMap.insert (vals, k, v)}
        fun insertType {types, vals} (k, v) = {types = NameSortedMap.insert (types, k, v), vals}

        fun lookupVal ({types = _, vals}, name) = NameSortedMap.lookup (vals, name)
        fun lookupType ({types, vals = _}, name) = NameSortedMap.lookup (types, name)
    end

    structure TC = TypecheckingCst
    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term

    type env = (FFType.def, FFType.typ FFTerm.def) Env.t

    fun pushTypes env types =
        let fun step (var, {binder = {kind, typ = _}, shade = _}, env) =
                Env.insertType env (var, {var, kind})
        in NameHashTable.foldi step env types
        end

    fun typeToUnFixedF (env: env) (typ: TC.typ): FFType.typ FAst.Type.typ =
        case typ
        of TC.OutputType typ =>
            (case typ
             of FFType.ForAll (pos, {var, ...}, body) =>
                 FFType.ForAll (pos, Env.lookupType (env, var), typRefToF env body)
              | FFType.Arrow (pos, {domain, codomain}) =>
                 FFType.Arrow (pos, {domain = typRefToF env domain, codomain = typRefToF env codomain})
              | FFType.Type (pos, typ) => FFType.Type (pos, typRefToF env typ)
              | FFType.UseT (pos, {var, ...}) => FFType.UseT (pos, Env.lookupType (env, var))
              | FFType.Prim (pos, p) => FFType.Prim (pos, p))
         | TC.InputType _ => raise Fail "unreachable"
         | TC.ScopeType {typ, types, parent = _} => typeToUnFixedF (pushTypes env types) (!typ)
         | TC.OVar (_, ov) => FFType.UseT (Pos.default "FIXME", Env.lookupType (env, TypeVars.ovName ov))
         | TC.UVar (_, uv) => (case TypeVars.uvGet uv
                               of Either.Right t => typeToUnFixedF env t
                                | Either.Left uv => FFType.Prim (Pos.default "FIXME", FFType.Unit))

    and typeToF (env: env) (typ: TC.typ): FFType.typ = FFType.Fix (typeToUnFixedF env typ)

    and typRefToF (env: env) (typ: TC.typ ref): FFType.typ = typeToF env (!typ)

    fun pushVals env vals =
        let fun step (var, {binder = {typ, value = _}, shade = _}, env) =
                Env.insertVal env (var, {var, typ = typeToF env (valOf (!typ))})
        in NameHashTable.foldi step env vals
        end

    fun toUnfixedF (env: env) (expr: TC.expr ref): (FFType.typ, FFTerm.expr) FAst.Term.expr =
        case !expr
        of TC.OutputExpr expr =>
            (case expr
             of FFTerm.Fn (pos, {var, typ = _}, body) =>
                 FFTerm.Fn (pos, Env.lookupVal (env, var), exprToF env body)
              | FFTerm.TFn (pos, {var, ...}, body) =>
                 FFTerm.TFn (pos, Env.lookupType (env, var), exprToF env body)
              | FFTerm.Let (pos, stmts, body) =>
                 FFTerm.Let (pos, Vector.map (stmtToF env) stmts, exprToF env body)
              | FFTerm.App (pos, typ, {callee, arg}) =>
                 FFTerm.App (pos, typRefToF env typ, {callee = exprToF env callee, arg = exprToF env arg})
              | FFTerm.TApp (pos, typ, {callee, arg}) =>
                 FFTerm.TApp (pos, typRefToF env typ, {callee = exprToF env callee, arg = typRefToF env arg})
              | FFTerm.Type (pos, typ) => FFTerm.Type (pos, typRefToF env typ)
              | FFTerm.Use (pos, {var, ...}) => FFTerm.Use (pos, Env.lookupVal (env, var))
              | FFTerm.Const (pos, c) => FFTerm.Const (pos, c))
         | TC.ScopeExpr {expr, vals, parent = _} => toUnfixedF (pushVals env vals) expr
         | TC.InputExpr _ => raise Fail "unreachable"

    and exprToF (env: env) (expr: TC.expr ref): FFTerm.expr = FFTerm.Fix (toUnfixedF env expr)

    and stmtToF (env: env) stmt =
        case stmt
        of FFTerm.Val (pos, {var, typ = _}, expr) =>
            FFTerm.Val (pos, Env.lookupVal (env, var), exprToF env expr)
         | FFTerm.Expr expr => FFTerm.Expr (exprToF env expr)

    val toF = exprToF Env.empty
end

