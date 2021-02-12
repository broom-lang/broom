module Subst : sig
    type t
end

type 'a t

val ref : 'a -> 'a t
val (!) : 'a t -> 'a
val (:=) : 'a t -> 'a -> unit

