module rec Type : (FcSigs.TYPE
    with type uv = Uv.t
    with type subst = Uv.subst)

and Uv : (FcSigs.UV with type typ = Type.t)

module Term : FcSigs.TERM with module Type = Type

