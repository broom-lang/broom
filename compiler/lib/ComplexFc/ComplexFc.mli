module Type = GraphType

module Term : ComplexFcSigs.TERM with type Expr.typ = Type.Type.t

module Program : ComplexFcSigs.PROGRAM
    with module Term = Term

