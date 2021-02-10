module Subst : sig
    type t
end

type 'a t

val equal : 'a t -> 'a t -> bool

val ref : 'a -> 'a t
val (!) : 'a t -> 'a
val (:=) : 'a t -> 'a -> unit

type 'a txref = 'a t

module type T = sig type t end

module Hashtbl : sig
    module Make (T : T) : CCHashtbl.S with type key = T.t t
end

module HashSet : sig
    module Make (T : T) : CCHashSet.S with type elt = T.t t
end

module Set : sig
    type 'a t

    val empty : 'a t
    val add : 'a txref -> 'a t -> 'a t
    val remove : 'a txref -> 'a t -> 'a t
    val is_empty : 'a t -> bool
    val mem : 'a txref -> 'a t -> bool

    val iter : ('a txref -> unit) -> 'a t -> unit
end

