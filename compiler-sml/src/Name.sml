structure Name :> sig
    type t

    val fromString: string -> t
    val toString: t -> string
end = struct
    datatype t = String of string

    val fromString = String
    val toString = fn String s => s
end