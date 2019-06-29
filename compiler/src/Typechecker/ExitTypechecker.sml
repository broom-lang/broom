structure ExitTypechecker :> sig
    val exprToF: FlexFAst.Term.expr -> FixedFAst.Term.expr
    val stmtToF: FlexFAst.Term.stmt -> FixedFAst.Term.stmt
end = struct
    datatype sv = datatype FlexFAst.Type.sv
    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term
    datatype concr = datatype FlexFAst.Type.concr'
    datatype abs = datatype FlexFAst.Type.abs'
    datatype expr = datatype FlexFAst.Term.expr
    datatype stmt = datatype FlexFAst.Term.stmt
    datatype either = datatype Either.t

    val rec concrToF: FlexFAst.Type.concr -> FFType.concr =
        fn ForAll (pos, param, body) => ForAll (pos, param, concrToF body)
         | Arrow (pos, {domain, codomain}) =>
            Arrow (pos, {domain = concrToF domain, codomain = concrToF codomain})
         | Record (pos, row) => Record (pos, concrToF row)
         | RowExt (pos, {field = (label, fieldt), ext}) =>
            RowExt (pos, {field = (label, concrToF fieldt), ext = concrToF ext})
         | EmptyRow pos => EmptyRow pos
         | CallTFn (pos, f, args) =>
            CallTFn (pos, f, Vector.map concrToF args)
         | FFType.Type (pos, typ) => FFType.Type (pos, absToF typ)
         | UseT (pos, def) => UseT (pos, def)
         | Prim (pos, p) => Prim (pos, p)
         | SVar (pos, UVar uv) => (case TypeVars.Uv.get uv
                                   of Right t => concrToF t
                                    | Left _ => Prim (pos, FFType.Prim.Unit))
         | SVar (pos, Path path) => (case TypeVars.Path.get (Fn.constantly false) path (* FIXME *)
                                     of Right (t, _) => concrToF t
                                      | Left (t, _) => concrToF t)

    and absToF: FlexFAst.Type.abs -> FFType.abs =
        fn Exists (pos, params, body) => Exists (pos, params, concrToF body)

    val rec exprToF: FlexFAst.Term.expr -> FFTerm.expr =
        fn Fn (pos, {var, typ}, body) =>
            FFTerm.Fn (pos, {var, typ = concrToF typ}, exprToF body)
         | TFn (pos, param, body) => FFTerm.TFn (pos, param, exprToF body)
         | Extend (pos, typ, fields, record) =>
            FFTerm.Extend ( pos, concrToF typ
                          , Vector.map (Pair.second (exprToF)) fields
                          , Option.map (exprToF) record)
         | Let (pos, stmts, body) =>
            FFTerm.Let (pos, Vector.map (stmtToF) stmts, exprToF body)
         | If (pos, cond, conseq, alt) =>
            FFTerm.If (pos, exprToF cond, exprToF conseq, exprToF alt)
         | App (pos, typ, {callee, arg}) =>
            FFTerm.App (pos, concrToF typ, {callee = exprToF callee, arg = exprToF arg})
         | TApp (pos, typ, {callee, args}) =>
            FFTerm.TApp (pos, concrToF typ, {callee = exprToF callee, args = Vector.map concrToF args})
         | Field (pos, typ, expr, label) =>
            FFTerm.Field (pos, concrToF typ, exprToF expr, label)
         | Type (pos, typ) => FFTerm.Type (pos, absToF typ)
         | Use (pos, {var, typ}) => FFTerm.Use (pos, {var, typ = concrToF typ})
         | Const (pos, c) => FFTerm.Const (pos, c)

    and stmtToF =
        fn Val (pos, {var, typ}, expr) => FFTerm.Val (pos, {var, typ = concrToF typ}, exprToF expr)
         | Axiom (pos, name, typ) => FFTerm.Axiom (pos, name, concrToF typ) (* FIXME *)
         | Expr expr => FFTerm.Expr (exprToF expr)
end

