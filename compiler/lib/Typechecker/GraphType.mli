module rec Typ : (GraphTypeSigs.TYPE
    with type uv = Uv.t
    with type bound = Uv.bound
    with type binder = Uv.binder
    with type scope = Uv.scope
    with type ov = Ov.t)

and Uv : (GraphTypeSigs.UV
    with type typ = Typ.t
    with type kind = Typ.kind
    with type ov = Ov.t)

and Ov : GraphTypeSigs.OV
    with type kind = Typ.kind
    with type scope = Uv.scope

module Type : sig
    (* `struct include` strengthens types so that `Type.t` = `Typ.t` etc.: *)
    include module type of struct include Typ end

    val aType : t
    val aKind : t
    val aRow : t
    val rep : t
end

