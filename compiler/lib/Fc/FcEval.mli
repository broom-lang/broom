module Env : sig
    type t

    val eval : unit -> t
    val interactive : unit -> t
end

module Value : sig
    type t =
        | Tuple of t Vector.t
        | Fn of ((t -> t) -> t -> t)
        | Record of t Name.Map.t
        | Proxy
        | Cell of t option ref
        | Int of int

    val to_doc : t -> PPrint.document
end

val run : Env.t -> Fc.Program.t -> Value.t * Env.t

