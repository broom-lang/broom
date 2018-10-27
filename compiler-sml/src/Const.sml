structure Const :> sig
    datatype t = Int of int

    val toString: t -> string
end = struct
    datatype t = Int of int

    val toString = fn Int n => Int.toString n (* HACK *)
end