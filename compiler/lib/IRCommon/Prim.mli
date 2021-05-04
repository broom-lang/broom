type t =
    | Unit
    | Int | Bool
    | Array | String | Cell
    | Rep (* = *) | Boxed | UnitRep | PairRep
    | TypeIn | RowOf

val grammar : t Grammar.t

val to_doc : t -> PPrint.document

val eq : t -> t -> bool

