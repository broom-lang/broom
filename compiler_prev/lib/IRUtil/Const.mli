type t =
    | Int of int
    | String of string

val grammar : t Grammar.t
val to_doc : t -> PPrint.document

