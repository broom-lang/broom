type log
type 'a ref

val log : unit -> log
val transaction : log -> (unit -> 'a) -> 'a

val ref : 'a -> 'a ref
val get : 'a ref -> 'a
val set : log -> 'a ref -> 'a -> unit

