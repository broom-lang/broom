structure Const :> sig
    datatype t = Int of int

    val toString: t -> string
    val toDoc: t -> PPrint.t
    val typeOf: t -> PrimType.t
end = struct
    datatype t = Int of int

    val toString = fn Int n => Int.toString n (* HACK *)
    
    structure ToDoc = ToDocFromToString(struct type t = t val toString = toString end)
    val toDoc = ToDoc.toDoc

    val typeOf = fn Int _ => PrimType.I32
end
