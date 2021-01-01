type _ t = private
    | Map : ('a, 'b) PIso.t * 'a t -> 'b t
    | AndThen : 'a t * 'b t -> ('a * 'b) t
    | Pure : 'a -> 'a t
    | Either : 'a t * 'a t -> 'a t
    | Fail : 'a t
    | Fix : ('a t -> 'a t) -> 'a t
    | Token : char t

val map : ('a, 'b) PIso.t -> 'a t -> 'b t
val and_then : 'a t -> 'b t -> ('a * 'b) t
val pure : 'a -> 'a t

val either : 'a t -> 'a t -> 'a t
val fail : 'a t

val fix : ('a t -> 'a t) -> 'a t

val opt : 'a t -> 'a option t
val many : 'a t -> 'a list t
val many1 : 'a t -> 'a list t

val char : char t

val token : char -> unit t
val text : string -> unit t

val digit : char t
val int : int t

module Infix : sig
    val (<$>) : ('a, 'b) PIso.t -> 'a t -> 'b t
    val (<*>) : 'a t -> 'b t -> ('a * 'b) t
    val (<*) : 'a t -> unit t -> 'a t
    val ( *> ) : unit t -> 'b t -> 'b t
    val (<|>) : 'a t -> 'a t -> 'a t
end

