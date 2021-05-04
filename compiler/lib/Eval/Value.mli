type t =
    | Fn of ((t -> t) -> t -> t)
    | Pair of {fst : t; snd : t}
    | Unit
    | Record of t Name.Map.t
    | Proxy
    | Cell of t option ref
    | Int of int
    | Bool of bool
    | String of string

val to_doc : t -> PPrint.document

