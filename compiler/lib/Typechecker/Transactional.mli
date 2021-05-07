val transaction : (unit -> 'a option) -> 'a option

module Ref : sig
    type 'a t

    val ref : 'a -> 'a t
    val (!) : 'a t -> 'a
    val (:=) : 'a t -> 'a -> unit

    val eq : 'a t -> 'a t -> bool
end

module Queue : sig
    type 'a t

    val create : unit -> 'a t
    val push : 'a t -> 'a -> unit
    val pop : 'a t -> 'a option
end

