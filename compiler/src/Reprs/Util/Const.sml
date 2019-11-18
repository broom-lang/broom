structure Const :> sig
    datatype t = Int of int
               | Bool of bool

    val toString: t -> string
    val toDoc: t -> PPrint.t
    val typeOf: t -> PrimType.t
end = struct
    datatype t = Int of int
               | Bool of bool

    val toString = fn Int n => Int.toString n (* HACK *)
                    | Bool true => "True"
                    | Bool false => "False"

    val toDoc = PPrint.text o toString

    val typeOf = fn Int _ => PrimType.I32
                  | Bool _ => PrimType.Bool
end
