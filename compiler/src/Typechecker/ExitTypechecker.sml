structure ExitTypechecker :> sig
    type env = (FlexFAst.Type.concr, FlexFAst.Term.expr, TypeError.t) TypecheckingEnv.t

    val exprToF: env -> FlexFAst.Term.expr -> FixedFAst.Term.expr
    val stmtToF: env -> FlexFAst.Term.stmt -> FixedFAst.Term.stmt
    val programToF: env -> FlexFAst.Term.program -> FixedFAst.Term.program
end = struct
    datatype sv = datatype FlexFAst.Type.sv
    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term
    datatype concr = datatype FlexFAst.Type.concr'
    datatype co = datatype FlexFAst.Type.co'
    datatype expr = datatype FlexFAst.Term.expr
    datatype stmt = datatype FlexFAst.Term.stmt
    datatype pat = datatype FlexFAst.Term.pat
    datatype either = datatype Either.t
    type env = (FlexFAst.Type.concr, FlexFAst.Term.expr, TypeError.t) TypecheckingEnv.t

    fun concrToF env: FlexFAst.Type.concr -> FFType.concr =
        fn Exists (params, body) => Exists (params, concrToF env body)
         | ForAll (params, body) => ForAll (params, concrToF env body)
         | Arrow (expl, {domain, codomain}) =>
            Arrow (expl, {domain = concrToF env domain, codomain = concrToF env codomain})
         | FType.Record row => FType.Record (concrToF env row)
         | RowExt {base, field = (label, fieldt)} =>
            RowExt {base = concrToF env base, field = (label, concrToF env fieldt)}
         | EmptyRow => EmptyRow
         | FFType.App {callee, args} =>
            FFType.App {callee = concrToF env callee, args = Vector1.map (concrToF env) args}
         | CallTFn name => CallTFn name
         | FFType.Type typ => FFType.Type (concrToF env typ)
         | UseT def => UseT def
         | Prim p => Prim p
         | SVar (UVar uv) => uvToF env uv
         | SVar (Path path) => (case TypeVars.Path.get env path
                                of Right (uv, _) => uvToF env uv
                                 | Left t => concrToF env t)

    and coercionToF env: FlexFAst.Type.co -> FFType.co =
        fn Refl t => Refl (concrToF env t)
         | Symm co => Symm (coercionToF env co)
         | InstCo {callee, args} =>
            InstCo {callee = coercionToF env callee, args = Vector1.map (concrToF env) args}
         | UseCo name => UseCo name

    and uvToF env uv =
        case TypeVars.Uv.get env uv
        of Right t => concrToF env t
         | Left uv => FType.kindDefault (TypeVars.Uv.kind env uv)

    fun exprToF env: FlexFAst.Term.expr -> FFTerm.expr =
        fn Fn (pos, {pos = defPos, id, var, typ}, expl, body) =>
            FFTerm.Fn (pos, {pos = defPos, id, var, typ = concrToF env typ}, expl, exprToF env body)
         | TFn (pos, param, body) => FFTerm.TFn (pos, param, exprToF env body)
         | EmptyRecord pos => FFTerm.EmptyRecord pos
         | With (pos, typ, {base, field}) =>
            FFTerm.With (pos, concrToF env typ, {base = exprToF env base, field = Pair.second (exprToF env) field})
         | Where (pos, typ, {base, field}) =>
            FFTerm.Where (pos, concrToF env typ, {base = exprToF env base, field = Pair.second (exprToF env) field})
         | Without (pos, typ, {base, field}) =>
            FFTerm.Without (pos, concrToF env typ, {base = exprToF env base, field})
         | Letrec (pos, stmts, body) =>
            FFTerm.Letrec (pos, Vector1.map (stmtToF env) stmts, exprToF env body)
         | Let (pos, stmts, body) =>
            FFTerm.Let (pos, Vector1.map (stmtToF env) stmts, exprToF env body)
         | Match (pos, typ, matchee, clauses) =>
            FFTerm.Match (pos, concrToF env typ, exprToF env matchee, Vector.map (clauseToF env) clauses)
         | App (pos, typ, {callee, arg}) =>
            FFTerm.App (pos, concrToF env typ, {callee = exprToF env callee, arg = exprToF env arg})
         | TApp (pos, typ, {callee, args}) =>
            FFTerm.TApp (pos, concrToF env typ, {callee = exprToF env callee, args = Vector1.map (concrToF env) args})
         | PrimApp (pos, typ, opn, targs, args) =>
            FFTerm.PrimApp (pos, concrToF env typ, opn, Vector.map (concrToF env) targs, Vector.map (exprToF env) args)
         | Field (pos, typ, expr, label) =>
            FFTerm.Field (pos, concrToF env typ, exprToF env expr, label)
         | Cast (pos, typ, expr, coercion) =>
            FFTerm.Cast (pos, concrToF env typ, exprToF env expr, coercionToF env coercion)
         | Type (pos, typ) => FFTerm.Type (pos, concrToF env typ)
         | Use (pos, {pos = defPos, id, var, typ}) =>
            FFTerm.Use (pos, {pos = defPos, id, var, typ = concrToF env typ})
         | Const (pos, c) => FFTerm.Const (pos, c)

    and clauseToF env = fn {pattern, body} => {pattern = patternToF env pattern, body = exprToF env body}

    and patternToF env =
        fn Def (pos, {pos = defPos, id, var, typ}) =>
            FFTerm.Def (pos, {pos = defPos, id, var, typ = concrToF env typ})
         | AnyP pos => FFTerm.AnyP pos
         | ConstP (pos, c) => FFTerm.ConstP (pos, c)

    and stmtToF env =
        fn Val (pos, {pos = defPos, id, var, typ}, expr) =>
            FFTerm.Val (pos, {pos = defPos, id, var, typ = concrToF env typ}, exprToF env expr)
         | Axiom (pos, name, l, r) => FFTerm.Axiom (pos, name, concrToF env l, concrToF env r)
         | Expr expr => FFTerm.Expr (exprToF env expr)

    fun programToF env {typeFns, code = (codePos, defns, body), sourcemap} =
        { typeFns
        , code = (codePos, Vector1.map (stmtToF env) defns, exprToF env body)
        , sourcemap }
end

