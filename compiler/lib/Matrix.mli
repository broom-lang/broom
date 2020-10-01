type 'a t

val of_col : 'a Vector.t -> 'a t
val of_rows : 'a Vector.t Streaming.Stream.t -> 'a t

val height : 'a t -> int
val width : 'a t -> int

val get : row: int -> col: int -> 'a t -> 'a option
val row : int -> 'a t -> 'a Streaming.Source.t option
val col : int -> 'a t -> 'a Streaming.Source.t option

val select_rows : IntSet.t -> 'a t -> 'a t
val remove_col : int -> 'a t -> 'a t

