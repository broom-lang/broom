type t =
    | Tuple of t Vector.t
    | Fn of ((t -> t) -> t -> t)
    | Record of t Name.Map.t
    | Proxy
    | Cell of t option ref
    | Int of int
    | Bool of bool
    | String of string

val to_doc : t -> PPrint.document

