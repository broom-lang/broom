module Type = FcType.Type

module Term : FcSigs.TERM with module Type = FcType.Typ

module Program : FcSigs.PROGRAM
    with module Type = Type
    with module Term = Term

