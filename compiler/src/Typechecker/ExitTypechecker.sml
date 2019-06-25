structure ExitTypechecker :> sig
    val exprToF: FlexFAst.Term.expr -> FixedFAst.Term.expr
    val stmtToF: FlexFAst.Term.stmt -> FixedFAst.Term.stmt
end = struct
    datatype sv = datatype FlexFAst.Type.sv
    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term
    datatype concr = datatype FAst.Type.concr
    datatype abs = datatype FAst.Type.abs
    datatype expr = datatype FAst.Term.expr
    datatype stmt = datatype FAst.Term.stmt
    datatype either = datatype Either.t

    val rec concrToF: FlexFAst.Type.concr -> FFType.concr =
        fn ForAll (pos, param, body) => ForAll (pos, param, concrToF body)
         | Arrow (pos, {domain, codomain}) =>
            Arrow (pos, {domain = concrToF domain, codomain = concrToF codomain})
         | Record (pos, row) => Record (pos, concrToF row)
         | RowExt (pos, {field = (label, fieldt), ext}) =>
            RowExt (pos, {field = (label, concrToF fieldt), ext = concrToF ext})
         | EmptyRow pos => EmptyRow pos
         | FFType.Type (pos, typ) => FFType.Type (pos, absToF typ)
         | UseT (pos, def) => UseT (pos, def)
         | Prim (pos, p) => Prim (pos, p)
         (* HACK: *)
         | SVar (pos, UVar uv) => (case TypeVars.uvGet uv
                                   of Right t => concrToF t
                                    | Left _ => Prim (pos, FFType.Prim.Unit))

    and absToF: FlexFAst.Type.abs -> FFType.abs =
        fn Exists (pos, params, body) => Exists (pos, params, concrToF body)

    val rec exprToF: FlexFAst.Term.expr -> FFTerm.expr =
        fn Fn (pos, {var, typ}, body) =>
            Fn (pos, {var, typ = concrToF typ}, exprToF body)
         | TFn (pos, param, body) => TFn (pos, param, exprToF body)
         | Extend (pos, typ, fields, record) =>
            Extend ( pos, concrToF typ
                   , Vector.map (Pair.second (exprToF)) fields
                   , Option.map (exprToF) record)
         | Let (pos, stmts, body) =>
            Let (pos, Vector.map (stmtToF) stmts, exprToF body)
         | If (pos, cond, conseq, alt) =>
            If (pos, exprToF cond, exprToF conseq, exprToF alt)
         | App (pos, typ, {callee, arg}) =>
            App (pos, concrToF typ, {callee = exprToF callee, arg = exprToF arg})
         | TApp (pos, typ, {callee, args}) =>
            TApp (pos, concrToF typ, {callee = exprToF callee, args = Vector.map concrToF args})
         | Field (pos, typ, expr, label) =>
            Field (pos, concrToF typ, exprToF expr, label)
         | Type (pos, typ) => Type (pos, absToF typ)
         | Use (pos, {var, typ}) => Use (pos, {var, typ = concrToF typ})
         | Const (pos, c) => Const (pos, c)

    and stmtToF =
        fn Val (pos, {var, typ}, expr) => Val (pos, {var, typ = concrToF typ}, exprToF expr)
         | Expr expr => Expr (exprToF expr)
end

