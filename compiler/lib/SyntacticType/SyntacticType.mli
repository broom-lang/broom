type t =
    | Ov of {name : Name.t; kind : kind}
    | Bv of {depth : int; sibli : int; kind : kind}
    | Exists of {existentials : kind Vector1.t; body : t}
    | Pi of {universals : kind Vector.t; domain : t; codomain : t}
    | Fn of {param : kind; body : t}
    | App of {callee : t; arg : t}
    | Record of t
    | With of {base : t; label : Name.t; field : t}
    | EmptyRow
    | Tuple of t Vector.t
    | Proxy of t
    | PromotedTuple of t Vector.t
    | PromotedArray of t Vector.t
    | Prim of Prim.t

and kind = t

val to_doc : t -> PPrint.document

val expose : t Vector.t -> t -> t
val close : int Name.HashMap.t -> t -> t

