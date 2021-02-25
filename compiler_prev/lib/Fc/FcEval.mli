module Namespace : sig
    type t

    val create : unit -> t
end

module Value : sig
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
end

val run : Namespace.t -> Fc.Program.t -> Namespace.t * Value.t

