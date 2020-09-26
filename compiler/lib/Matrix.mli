type 'a t

val of_col : 'a Vector.t -> 'a t

val get : row: int -> col: int -> 'a t -> 'a option
val row : int -> 'a t -> 'a Streaming.Source.t option
val col : int -> 'a t -> 'a Streaming.Source.t option

