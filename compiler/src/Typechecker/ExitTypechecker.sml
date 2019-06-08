structure ExitTypechecker :> sig
    val exprToF: TypecheckingCst.typ FAst.Term.expr -> FixedFAst.Term.expr
end = struct
    structure TC = TypecheckingCst
    datatype tc_typ = datatype TC.typ
    datatype tc_expr = datatype TC.expr
    structure FFType = FixedFAst.Type
    datatype typ = datatype FAst.Type.typ
    structure FFTerm = FixedFAst.Term
    datatype expr = datatype FAst.Term.expr
    datatype stmt = datatype FAst.Term.stmt
    datatype either = datatype Either.t

    fun typeToUnFixedF (typ: TC.typ): FFType.typ FAst.Type.typ =
        case typ
        of OutputType typ =>
            (case typ
             of ForAll (pos, param, body) => ForAll (pos, param, typeToF body)
              | Arrow (pos, {domain, codomain}) =>
                 Arrow (pos, {domain = typeToF domain, codomain = typeToF codomain})
              | Record (pos, row) => Record (pos, typeToF row)
              | RowExt (pos, {field = (label, fieldt), ext}) =>
                 RowExt (pos, {field = (label, typeToF fieldt), ext = typeToF ext})
              | EmptyRow pos => EmptyRow pos
              | FFType.Type (pos, typ) => FFType.Type (pos, typeToF typ)
              | UseT (pos, def) => UseT (pos, def)
              | Prim (pos, p) => Prim (pos, p))
         | InputType _ => raise Fail "unreachable"
         | ScopeType {typ, ...} => typeToUnFixedF typ
         (* HACK: *)
         | OVar (pos, ov) => UseT (pos, {var = TypeVars.ovName ov, kind = FFType.TypeK pos})
         | UVar (pos, uv) => (case TypeVars.uvGet uv
                               of Right t => typeToUnFixedF t
                                | Left _ => Prim (pos, FFType.Prim.Unit))

    and typeToF (typ: TC.typ): FFType.typ = FFType.Fix (typeToUnFixedF typ)

    val rec exprToF: TC.typ FAst.Term.expr -> FFTerm.expr =
        fn Fn (pos, {var, typ}, body) =>
            Fn (pos, {var, typ = typeToF typ}, exprToF body)
         | TFn (pos, param, body) => TFn (pos, param, exprToF body)
         | Extend (pos, typ, fields, record) =>
            Extend ( pos, typeToF typ
                   , Vector.map (Pair.second (exprToF)) fields
                   , Option.map (exprToF) record)
         | Let (pos, stmts, body) =>
            Let (pos, Vector.map (stmtToF) stmts, exprToF body)
         | If (pos, cond, conseq, alt) =>
            If (pos, exprToF cond, exprToF conseq, exprToF alt)
         | App (pos, typ, {callee, arg}) =>
            App (pos, typeToF typ, {callee = exprToF callee, arg = exprToF arg})
         | TApp (pos, typ, {callee, arg}) =>
            TApp (pos, typeToF typ, {callee = exprToF callee, arg = typeToF arg})
         | Field (pos, typ, expr, label) =>
            Field (pos, typeToF typ, exprToF expr, label)
         | Type (pos, typ) => Type (pos, typeToF typ)
         | Use (pos, {var, typ}) => Use (pos, {var, typ = typeToF typ})
         | Const (pos, c) => Const (pos, c)

    and stmtToF =
        fn Val (pos, {var, typ}, expr) => Val (pos, {var, typ = typeToF typ}, exprToF expr)
         | Expr expr => Expr (exprToF expr)
end

