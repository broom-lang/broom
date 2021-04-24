type t' =
    | Unbound of Name.t

type t = t' Util.with_pos

val to_doc : t -> PPrint.document

