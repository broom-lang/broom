val transaction : (unit -> 'a) -> 'a

module Ref : sig
    type 'a t

    val ref : 'a -> 'a t
    val (!) : 'a t -> 'a
    val (:=) : 'a t -> 'a -> unit

    val eq : 'a t -> 'a t -> bool
end

