module T = Fc.Type

type t' =
    | Subtype of T.t * T.t
    | Unify of T.t * T.t
    | Unbound of Name.t
    | Occurs of T.uv * T.t
    | IncompleteImpl of T.uv * T.uv

type t = t' Util.with_pos

val to_doc : t -> PPrint.document

