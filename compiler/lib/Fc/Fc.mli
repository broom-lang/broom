module Type = FcType.Type
module Uv = FcType.Uv

module Term : FcSigs.TERM with type Expr.typ = Type.t

module Program : FcSigs.PROGRAM
    with module Term = Term

