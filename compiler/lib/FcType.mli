module rec Typ : (FcTypeSigs.TYPE
    with type uv = Uv.t
    with type subst = Uv.subst)

and Uv : (FcTypeSigs.UV
    with type kind = Typ.kind
    with type typ = Typ.t
    with type level = Typ.level)

module Type : sig
    (* `struct include` strengthens types so that `Type.t` = `Typ.t` etc.: *)
    include module type of struct include Typ end

    val aType : t
    val aKind : t
    val aRow : t
    val rep : t
end

