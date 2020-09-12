module rec Type : (FcTypeSigs.TYPE
    with type uv = Uv.t
    with type subst = Uv.subst)

and Uv : (FcTypeSigs.UV
    with type kind = Type.kind
    with type typ = Type.t
    with type level = Type.level)

