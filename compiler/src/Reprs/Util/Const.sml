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
    
    structure ToDoc = ToDocFromToString(struct type t = t val toString = toString end)
    val toDoc = ToDoc.toDoc

    val typeOf = fn Int _ => PrimType.I32
                  | Bool _ => PrimType.Bool
end
