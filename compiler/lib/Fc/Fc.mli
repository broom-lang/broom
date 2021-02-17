module Type = GraphType

module Term : FcSigs.TERM with type Expr.typ = Type.Type.t

module Program : FcSigs.PROGRAM
    with module Term = Term

