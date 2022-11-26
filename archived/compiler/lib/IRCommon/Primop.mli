type t =
    | Pair | Fst | Snd
    | CellNew | CellInit | CellGet
    | Int | String | Type
    | TypeOf
    | Import
    | GlobalSet | GlobalGet

val of_string : string -> t option
val to_string : t -> string
val to_doc : t -> PPrint.document

val is_pure : t -> bool

