structure Const :> sig
    datatype t = Int of int

    val toString: t -> string
    val typeOf: t -> PrimType.t
end = struct
    datatype t = Int of int

    val toString = fn Int n => Int.toString n (* HACK *)

    val typeOf = fn Int _ => PrimType.I32
end
