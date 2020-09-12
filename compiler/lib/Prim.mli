type t =
    | Int
    | Type | Row

val to_doc : t -> PPrint.document

val eq : t -> t -> bool

