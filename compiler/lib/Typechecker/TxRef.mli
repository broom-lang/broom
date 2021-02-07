module Subst : sig
    type t
end

type 'a t

val equal : 'a t -> 'a t -> bool

val ref : 'a -> 'a t
val (!) : 'a t -> 'a
val (:=) : 'a t -> 'a -> unit

module Hashtbl : sig
    module Make (T : sig type t end) : CCHashtbl.S with type key = T.t t
end

