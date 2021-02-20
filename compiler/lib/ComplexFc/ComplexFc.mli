module Typ = GraphType.Typ

module Term : ComplexFcSigs.TERM
    with type Expr.typ = Typ.t
    with type Expr.coercion = Typ.coercion
    with type Expr.t_scope = GraphType.Uv.Scope.t

module Type : sig
    (* `struct include` strengthens types so that `Type.t` = `Typ.t` etc.: *)
    include module type of struct include Typ end

    val aType : t
    val aKind : t
    val aRow : t
    val rep : t
end

module Program : ComplexFcSigs.PROGRAM
    with module Term = Term

