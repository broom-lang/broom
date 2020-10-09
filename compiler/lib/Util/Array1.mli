type 'a t

val length : 'a t -> int
val get : 'a t -> int -> 'a

val of_array : 'a array -> 'a t option
val to_list : 'a t -> 'a list
val to_source : 'a t -> 'a Streaming.Source.t

val map : ('a -> 'b) -> 'a t -> 'b t

