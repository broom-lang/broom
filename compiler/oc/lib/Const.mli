type t =
    | Int of int
    | Bool of bool

val to_doc : t -> PPrint.document

