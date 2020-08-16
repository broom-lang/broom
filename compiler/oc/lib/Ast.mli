type 'a with_pos = 'a Util.with_pos

module rec Term : (AstSigs.TERM with type typ = Type.t)

and Type : (AstSigs.TYPE with type expr = Term.expr and type stmt = Term.stmt and type pat = Term.expr)

