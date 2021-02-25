type _ t = private
    | Map : ('a, 'b) PIso.t * 'a t -> 'b t
    | AndThen : 'a t * 'b t -> ('a * 'b) t
    | Pure : 'a -> 'a t
    | Either : 'a t * 'a t -> 'a t
    | Fail : 'a t
    | Fix : ('a t -> 'a t) -> 'a t
    | Token : char t

    | Printer : ('a -> PPrint.document option) -> 'a t
    | Group : 'a t -> 'a t
    | Nest : int * 'a t -> 'a t

val map : ('a, 'b) PIso.t -> 'a t -> 'b t
val and_then : 'a t -> 'b t -> ('a * 'b) t
val pure : 'a -> 'a t

val either : 'a t -> 'a t -> 'a t
val fail : 'a t

val fix : ('a t -> 'a t) -> 'a t
val printer : ('a -> PPrint.document option) -> 'a t

val nest : int -> 'a t -> 'a t

val opt : 'a t -> 'a option t
val many : 'a t -> 'a list t
val many1 : 'a t -> 'a list t
val separate : unit t -> 'a t -> 'a list t
val separate1 : unit t -> 'a t -> 'a list t

val prefix : int -> int -> 'a t -> 'b t -> ('a * 'b) t
val infix : int -> int -> unit t -> 'a t -> 'b t -> ('a * 'b) t
val surround : int -> int -> unit t -> 'a t -> unit t -> 'a t
val surround_separate : int -> int -> 'a Vector.t t
    -> unit t -> unit t -> unit t
    -> 'a t -> 'a Vector.t t 

val char : char t

val sat : (char -> bool) -> char t
val token : char -> unit t
val text : string -> unit t

val digit : char t
val int : int t

val lparen : unit t
val rparen : unit t
val parens : 'a t -> 'a t
val lbracket : unit t
val rbracket : unit t
val brackets : 'a t -> 'a t
val lbrace : unit t
val rbrace : unit t
val braces : 'a t -> 'a t

val dot : unit t
val comma : unit t
val colon : unit t
val semi : unit t

val equals : unit t
val bar : unit t
val caret : unit t
val slash : unit t

val blank : int -> unit t
val break : int -> unit t

module Infix : sig
    val (<$>) : ('a, 'b) PIso.t -> 'a t -> 'b t
    val (<*>) : 'a t -> 'b t -> ('a * 'b) t
    val (<*) : 'a t -> unit t -> 'a t
    val ( *> ) : unit t -> 'b t -> 'b t
    val (<|>) : 'a t -> 'a t -> 'a t
end

