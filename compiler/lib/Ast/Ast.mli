type 'a with_pos = 'a Util.with_pos

module rec Term : (AstSigs.TERM with type Expr.typ = Type.t)

and Type : (AstSigs.TYPE
    with type expr = Term.Expr.t
    with type pat = Term.Expr.pat
    with type stmt = Term.Stmt.t)

