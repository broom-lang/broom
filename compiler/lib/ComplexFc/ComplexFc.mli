module Type = GraphType

module Term : ComplexFcSigs.TERM
    with type Expr.typ = Type.Type.t
    with type Expr.coercion = Type.Type.coercion
    with type Expr.t_scope = Type.Uv.Scope.t

module Program : ComplexFcSigs.PROGRAM
    with module Term = Term

