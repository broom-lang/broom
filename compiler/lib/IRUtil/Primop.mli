type t =
    | CellNew | CellInit | CellGet
    | Int
    | Type
    | GlobalSet | GlobalGet

val of_string : string -> t option
val to_doc : t -> PPrint.document

val is_pure : t -> bool

