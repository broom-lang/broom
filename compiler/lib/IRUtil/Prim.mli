type t =
    | Int | Bool
    | Array | String | Cell
    | SingleRep (* = *) | Boxed
    | TypeIn | RowOf

val grammar : t Grammar.t

val to_doc : t -> PPrint.document

val eq : t -> t -> bool

