structure Const :> sig
    datatype t = Int of int

    val toString: t -> string
    val typeOf: t -> NameFType.prim
end = struct
    datatype t = Int of int

    val toString = fn Int n => Int.toString n (* HACK *)

    val typeOf = fn Int _ => NameFType.I32
end
