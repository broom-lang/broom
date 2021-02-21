module rec Types : (ComplexFcSigs.TYPES with type Coercer.expr = Term.Expr.t)

and Term : ComplexFcSigs.TERM
    with type Expr.typ = Types.Typ.t
    with type Expr.coercion = Types.Typ.coercion
    with type Expr.t_scope = Types.Uv.Scope.t
    with type Expr.bound = Types.Uv.bound

module Type : sig
    (* `struct include` strengthens types so that `Type.t` = `Typ.t` etc.: *)
    include module type of struct include Types.Typ end

    val aType : t
    val aKind : t
    val aRow : t
    val rep : t
end

module Program : ComplexFcSigs.PROGRAM
    with module Term = Term

