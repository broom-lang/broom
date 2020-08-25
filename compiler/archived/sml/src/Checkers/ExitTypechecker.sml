structure ExitTypechecker :> sig
    type env = (FAst.Type.concr, FAst.Term.expr, TypeError.t) TypecheckingEnv.t

    val exprToF: env -> FAst.Term.expr -> FAst.Term.expr
    val stmtToF: env -> FAst.Term.stmt -> FAst.Term.stmt
    val programToF: env -> FAst.Term.program -> FAst.Term.program
end = struct
    datatype sv = datatype FAst.Type.sv
    structure FFType = FAst.Type
    structure FFTerm = FAst.Term
    datatype concr = datatype FAst.Type.concr'
    datatype co = datatype FAst.Type.co'
    datatype expr = datatype FAst.Term.expr
    datatype stmt = datatype FAst.Term.stmt
    datatype pat = datatype FAst.Term.pat
    datatype either = datatype Either.t
    type env = (FAst.Type.concr, FAst.Term.expr, TypeError.t) TypecheckingEnv.t

    fun concrToF env: FAst.Type.concr -> FFType.concr =
        fn Exists (params, body) => Exists (params, concrToF env body)
         | ForAll (params, body) => ForAll (params, concrToF env body)
         | Arrow (expl, {domain, codomain}) =>
            Arrow (expl, {domain = concrToF env domain, codomain = concrToF env codomain})
         | FTypeBase.Record row => FTypeBase.Record (concrToF env row)
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

    and coercionToF env: FAst.Type.co -> FFType.co =
        fn Refl t => Refl (concrToF env t)
         | Symm co => Symm (coercionToF env co)
         | InstCo {callee, args} =>
            InstCo {callee = coercionToF env callee, args = Vector1.map (concrToF env) args}
         | UseCo name => UseCo name

    and uvToF env uv =
        case TypeVars.Uv.get env uv
        of Right t => concrToF env t
         | Left uv => FTypeBase.kindDefault (TypeVars.Uv.kind env uv)

    fun exprToF env: FAst.Term.expr -> FFTerm.expr =
        fn Fn (pos, def, expl, body) =>
            FFTerm.Fn (pos, defToF env def, expl, exprToF env body)
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
         | PrimApp (pos, typ, opn, targs, args, clauses) =>
            FFTerm.PrimApp ( pos, concrToF env typ, opn, Vector.map (concrToF env) targs, Vector.map (exprToF env) args
                           , Option.map (fn ({def, body}, failure) =>
                                             ( {def = defToF env def, body = exprToF env body}
                                             , exprToF env failure )) clauses )
         | Field (pos, typ, expr, label) =>
            FFTerm.Field (pos, concrToF env typ, exprToF env expr, label)
         | Cast (pos, typ, expr, coercion) =>
            FFTerm.Cast (pos, concrToF env typ, exprToF env expr, coercionToF env coercion)
         | Type (pos, typ) => FFTerm.Type (pos, concrToF env typ)
         | Use (pos, {pos = defPos, id, var, typ}) =>
            FFTerm.Use (pos, {pos = defPos, id, var, typ = concrToF env typ})
         | Const (pos, c) => FFTerm.Const (pos, c)

    and defToF env {pos, id, var, typ} = {pos, id, var, typ = concrToF env typ}

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

