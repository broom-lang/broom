structure ExitTypechecker :> sig
    val exprToF: FlexFAst.Term.expr -> FixedFAst.Term.expr
    val stmtToF: FlexFAst.Term.stmt -> FixedFAst.Term.stmt
    val programToF: FlexFAst.Term.program -> FixedFAst.Term.program
end = struct
    datatype sv = datatype FlexFAst.Type.sv
    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term
    datatype concr = datatype FlexFAst.Type.concr'
    datatype abs = datatype FlexFAst.Type.abs'
    datatype co = datatype FlexFAst.Type.co'
    datatype expr = datatype FlexFAst.Term.expr
    datatype stmt = datatype FlexFAst.Term.stmt
    datatype pat = datatype FlexFAst.Term.pat
    datatype either = datatype Either.t

    val rec concrToF: FlexFAst.Type.concr -> FFType.concr =
        fn ForAll (param, body) => ForAll (param, concrToF body)
         | Arrow (expl, {domain, codomain}) =>
            Arrow (expl, {domain = concrToF domain, codomain = concrToF codomain})
         | Record row => Record (concrToF row)
         | RowExt {field = (label, fieldt), ext} =>
            RowExt {field = (label, concrToF fieldt), ext = concrToF ext}
         | EmptyRow => EmptyRow
         | FFType.App {callee, args} =>
            FFType.App {callee = concrToF callee, args = Vector.map concrToF args}
         | CallTFn (f, args) =>
            CallTFn (f, Vector.map concrToF args)
         | FFType.Type typ => FFType.Type (absToF typ)
         | UseT def => UseT def
         | Prim p => Prim p
         | SVar (UVar uv) => (case TypeVars.Uv.get uv
                              of Right t => concrToF t
                               | Left _ => Prim (FFType.Prim.Unit))
         | SVar (Path path) => (case TypeVars.Path.get (Fn.constantly false) path
                                of Right ((_, t), _) => concrToF t
                                 | Left (t, _) => concrToF t)

    and absToF: FlexFAst.Type.abs -> FFType.abs =
        fn Exists (params, body) => Exists (params, concrToF body)

    and coercionToF: FlexFAst.Type.co -> FFType.co =
        fn Refl t => Refl (concrToF t)
         | Symm co => Symm (coercionToF co)
         | AppCo {callee, args} =>
            AppCo {callee = coercionToF callee, args = Vector.map concrToF args}
         | UseCo name => UseCo name

    fun axiomToF (name, l, r) = (name, concrToF l, concrToF r)

    val rec exprToF: FlexFAst.Term.expr -> FFTerm.expr =
        fn Fn (pos, scopeId, {var, typ}, expl, body) =>
            FFTerm.Fn (pos, scopeId, {var, typ = concrToF typ}, expl, exprToF body)
         | TFn (pos, scopeId, param, body) => FFTerm.TFn (pos, scopeId, param, exprToF body)
         | Extend (pos, typ, fields, record) =>
            FFTerm.Extend ( pos, concrToF typ
                          , Vector.map (Pair.second exprToF) fields
                          , Option.map exprToF record)
         | Override (pos, typ, fields, ext) =>
            FFTerm.Override ( pos, concrToF typ
                            , Vector.map (Pair.second exprToF) fields
                            , exprToF ext )
         | Let (pos, scopeId, stmts, body) =>
            FFTerm.Let (pos, scopeId, Vector.map (stmtToF) stmts, exprToF body)
         | Match (pos, typ, matchee, clauses) =>
            FFTerm.Match (pos, concrToF typ, exprToF matchee, Vector.map clauseToF clauses)
         | App (pos, typ, {callee, arg}) =>
            FFTerm.App (pos, concrToF typ, {callee = exprToF callee, arg = exprToF arg})
         | TApp (pos, typ, {callee, args}) =>
            FFTerm.TApp (pos, concrToF typ, {callee = exprToF callee, args = Vector.map concrToF args})
         | Field (pos, typ, expr, label) =>
            FFTerm.Field (pos, concrToF typ, exprToF expr, label)
         | Cast (pos, typ, expr, coercion) =>
            FFTerm.Cast (pos, concrToF typ, exprToF expr, coercionToF coercion)
         | Type (pos, typ) => FFTerm.Type (pos, absToF typ)
         | Use (pos, {var, typ}) => FFTerm.Use (pos, {var, typ = concrToF typ})
         | Const (pos, c) => FFTerm.Const (pos, c)

    and clauseToF = fn {pattern, body} => {pattern = patternToF pattern, body = exprToF body}

    and patternToF =
        fn AnnP (pos, {pat, typ}) => FFTerm.AnnP (pos, {pat = patternToF pat, typ = concrToF typ})
         | Def (pos, scopeId, {var, typ}) => FFTerm.Def (pos, scopeId, {var, typ = concrToF typ})
         | ConstP (pos, c) => FFTerm.ConstP (pos, c)

    and stmtToF =
        fn Val (pos, {var, typ}, expr) => FFTerm.Val (pos, {var, typ = concrToF typ}, exprToF expr)
         | Axiom (pos, name, l, r) => FFTerm.Axiom (pos, name, concrToF l, concrToF r)
         | Expr expr => FFTerm.Expr (exprToF expr)

    fun programToF {typeFns, axioms, scope, stmts} =
        { typeFns = typeFns
        , axioms = Vector.map axiomToF axioms
        , scope
        , stmts = Vector.map stmtToF stmts }
end

