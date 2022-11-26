module Type = FcType.Type

module Term = FcTerm

module Program : FcSigs.PROGRAM
    with module Term = Term

