structure ExitTypechecker :> sig
    val toF: TypecheckingCst.expr ref -> FixedFAst.Term.expr
end = struct
    structure Env :> sig
        type 'a t

        val empty: 'a t 
        val insert: 'a t -> Name.t * 'a -> 'a t
        val lookup: 'a t * Name.t -> 'a
    end = struct
        type 'a t = 'a NameSortedMap.map

        val empty = NameSortedMap.empty

        fun insert map (k, v) = NameSortedMap.insert (map, k, v)

        val lookup = NameSortedMap.lookup
    end

    structure TC = TypecheckingCst
    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term

    type venv = FFType.typ FFTerm.def Env.t

    fun typeToUnFixedF (typ: TC.typ): FFType.typ FAst.Type.typ =
        case typ
        of TC.OutputType typ =>
            (case typ
             of FFType.Arrow (pos, {domain, codomain}) =>
                 FFType.Arrow (pos, {domain = typRefToF domain, codomain = typRefToF codomain})
              | FFType.Prim (pos, p) => FFType.Prim (pos, p))
         | TC.InputType _ => raise Fail "unimplemented"

    and typeToF (typ: TC.typ): FFType.typ = FFType.Fix (typeToUnFixedF typ)

    and typRefToF (typ: TC.typ ref): FFType.typ = typeToF (!typ)

    fun pushVals env vals =
        let fun step (var, {binder = {typ, value = _}, shade = _}, env) =
                Env.insert env (var, {var, typ = typeToF (valOf (!typ))})
        in NameHashTable.foldi step env vals
        end

    fun toUnfixedF (env: venv) (expr: TC.expr ref): (FFType.typ, FFTerm.expr) FAst.Term.expr =
        case !expr
        of TC.OutputExpr expr =>
            (case expr
             of FFTerm.Fn (pos, {var, typ = _}, body) =>
                 FFTerm.Fn (pos, Env.lookup (env, var), exprToF env body)
              | FFTerm.Let (pos, stmts, body) =>
                 FFTerm.Let (pos, Vector.map (stmtToF env) stmts, exprToF env body)
              | FFTerm.App (pos, typ, {callee, arg}) =>
                 FFTerm.App (pos, typRefToF typ, {callee = exprToF env callee, arg = exprToF env arg})
              | FFTerm.Use (pos, {var, ...}) => FFTerm.Use (pos, Env.lookup (env, var))
              | FFTerm.Const (pos, c) => FFTerm.Const (pos, c))
         | TC.ScopeExpr {expr, vals, parent = _} => toUnfixedF (pushVals env vals) expr
         | TC.InputExpr _ => raise Fail "unreachable"

    and exprToF (env: venv) (expr: TC.expr ref): FFTerm.expr = FFTerm.Fix (toUnfixedF env expr)

    and stmtToF (env: venv) stmt =
        case stmt
        of FFTerm.Val (pos, {var, typ = _}, expr) =>
            FFTerm.Val (pos, Env.lookup (env, var), exprToF env expr)
         | FFTerm.Expr expr => FFTerm.Expr (exprToF env expr)

    val toF = exprToF Env.empty
end

