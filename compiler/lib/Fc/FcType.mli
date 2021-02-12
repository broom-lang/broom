module rec Typ : (FcTypeSigs.TYPE
    with type uv = Uv.t
    with type bound = Uv.bound
    with type binder = Uv.binder
    with type scope = Uv.scope)

and Uv : FcTypeSigs.UV
    with type typ = Typ.t
    with type kind = Typ.kind

module Type : sig
    (* `struct include` strengthens types so that `Type.t` = `Typ.t` etc.: *)
    include module type of struct include Typ end

    val aType : t
    val aKind : t
    val aRow : t
    val rep : t
end

