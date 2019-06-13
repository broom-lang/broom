structure ExitTypechecker :> sig
    val exprToF: TypecheckingCst.sv FAst.Term.expr -> FixedFAst.Term.expr
end = struct
    structure TC = TypecheckingCst
    datatype tc_typ = datatype TC.typ
    datatype tc_expr = datatype TC.expr
    datatype sv = datatype TC.sv
    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term
    datatype concr = datatype FAst.Type.concr
    datatype abs = datatype FAst.Type.abs
    datatype expr = datatype FAst.Term.expr
    datatype stmt = datatype FAst.Term.stmt
    datatype either = datatype Either.t

    val rec concrToF: TC.concr -> FFType.concr =
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
         | SVar (pos, OVar ov) => UseT (pos, {var = TypeVars.ovName ov, kind = FFType.TypeK pos})
         | SVar (pos, UVar uv) => (case TypeVars.uvGet uv
                                   of Right t => concrToF t
                                    | Left _ => Prim (pos, FFType.Prim.Unit))

    and absToF: TC.abs -> FFType.abs =
        fn Concr t => Concr (concrToF t)

    val rec exprToF: TC.sv FAst.Term.expr -> FFTerm.expr =
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
         | TApp (pos, typ, {callee, arg}) =>
            TApp (pos, concrToF typ, {callee = exprToF callee, arg = absToF arg})
         | Field (pos, typ, expr, label) =>
            Field (pos, concrToF typ, exprToF expr, label)
         | Type (pos, typ) => Type (pos, absToF typ)
         | Use (pos, {var, typ}) => Use (pos, {var, typ = concrToF typ})
         | Const (pos, c) => Const (pos, c)

    and stmtToF =
        fn Val (pos, {var, typ}, expr) => Val (pos, {var, typ = concrToF typ}, exprToF expr)
         | Expr expr => Expr (exprToF expr)
end

