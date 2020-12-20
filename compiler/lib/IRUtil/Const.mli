type t =
    | Int of int
    | String of string

val to_doc : t -> PPrint.document

