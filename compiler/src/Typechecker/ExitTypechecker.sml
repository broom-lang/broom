structure ExitTypechecker :> sig
    val exprToF: FlexFAst.Term.expr -> FixedFAst.Term.expr
    val stmtToF: FlexFAst.Term.stmt -> FixedFAst.Term.stmt
    val programToF: FlexFAst.Term.program -> FixedFAst.Term.program
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

    val rec concrToF: FlexFAst.Type.concr -> FFType.concr =
        fn Exists (params, body) => Exists (params, concrToF body)
         | ForAll (params, body) => ForAll (params, concrToF body)
         | Arrow (expl, {domain, codomain}) =>
            Arrow (expl, {domain = concrToF domain, codomain = concrToF codomain})
         | FType.Record row => FType.Record (concrToF row)
         | RowExt {base, field = (label, fieldt)} =>
            RowExt {base = concrToF base, field = (label, concrToF fieldt)}
         | EmptyRow => EmptyRow
         | FFType.App {callee, args} =>
            FFType.App {callee = concrToF callee, args = Vector1.map concrToF args}
         | CallTFn name => CallTFn name
         | FFType.Type typ => FFType.Type (concrToF typ)
         | UseT def => UseT def
         | Prim p => Prim p
         | SVar (UVar uv) => uvToF uv
         | SVar (Path path) => (case TypeVars.Path.get (Fn.constantly false) path
                                of Right (uv, _) => uvToF uv
                                 | Left t => concrToF t)

    and coercionToF: FlexFAst.Type.co -> FFType.co =
        fn Refl t => Refl (concrToF t)
         | Symm co => Symm (coercionToF co)
         | InstCo {callee, args} =>
            InstCo {callee = coercionToF callee, args = Vector1.map concrToF args}
         | UseCo name => UseCo name

    and uvToF = fn uv =>
        case TypeVars.Uv.get uv
        of Right t => concrToF t
         | Left uv => FType.kindDefault (TypeVars.Uv.kind uv)

    fun axiomToF (name, l, r) = (name, concrToF l, concrToF r)

    val rec exprToF: FlexFAst.Term.expr -> FFTerm.expr =
        fn Fn (pos, {pos = defPos, id, var, typ}, expl, body) =>
            FFTerm.Fn (pos, {pos = defPos, id, var, typ = concrToF typ}, expl, exprToF body)
         | TFn (pos, param, body) => FFTerm.TFn (pos, param, exprToF body)
         | EmptyRecord pos => FFTerm.EmptyRecord pos
         | With (pos, typ, {base, field}) =>
            FFTerm.With (pos, concrToF typ, {base = exprToF base, field = Pair.second exprToF field})
         | Where (pos, typ, {base, field}) =>
            FFTerm.Where (pos, concrToF typ, {base = exprToF base, field = Pair.second exprToF field})
         | Let (pos, stmts, body) =>
            FFTerm.Let (pos, Vector1.map (stmtToF) stmts, exprToF body)
         | Match (pos, typ, matchee, clauses) =>
            FFTerm.Match (pos, concrToF typ, exprToF matchee, Vector.map clauseToF clauses)
         | App (pos, typ, {callee, arg}) =>
            FFTerm.App (pos, concrToF typ, {callee = exprToF callee, arg = exprToF arg})
         | TApp (pos, typ, {callee, args}) =>
            FFTerm.TApp (pos, concrToF typ, {callee = exprToF callee, args = Vector1.map concrToF args})
         | Field (pos, typ, expr, label) =>
            FFTerm.Field (pos, concrToF typ, exprToF expr, label)
         | Cast (pos, typ, expr, coercion) =>
            FFTerm.Cast (pos, concrToF typ, exprToF expr, coercionToF coercion)
         | Type (pos, typ) => FFTerm.Type (pos, concrToF typ)
         | Use (pos, {pos = defPos, id, var, typ}) =>
            FFTerm.Use (pos, {pos = defPos, id, var, typ = concrToF typ})
         | Const (pos, c) => FFTerm.Const (pos, c)

    and clauseToF = fn {pattern, body} => {pattern = patternToF pattern, body = exprToF body}

    and patternToF =
        fn Def (pos, {pos = defPos, id, var, typ}) =>
            FFTerm.Def (pos, {pos = defPos, id, var, typ = concrToF typ})
         | ConstP (pos, c) => FFTerm.ConstP (pos, c)

    and stmtToF =
        fn Val (pos, {pos = defPos, id, var, typ}, expr) =>
            FFTerm.Val (pos, {pos = defPos, id, var, typ = concrToF typ}, exprToF expr)
         | Axiom (pos, name, l, r) => FFTerm.Axiom (pos, name, concrToF l, concrToF r)
         | Expr expr => FFTerm.Expr (exprToF expr)

    fun programToF {typeFns, stmts, sourcemap} =
        {typeFns, stmts = Vector.map stmtToF stmts, sourcemap}
end

