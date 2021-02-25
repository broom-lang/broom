type 'a t

val singleton : 'a -> 'a t

val length : 'a t -> int
val get : 'a t -> int -> 'a

val to_vector : 'a t -> 'a Vector.t
val of_vector : 'a Vector.t -> 'a t option
val to_array : 'a t -> 'a array
val of_list : 'a list -> 'a t option
val to_list : 'a t -> 'a list

val append : 'a t -> 'a t -> 'a t

val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val foldi : ('a -> int -> 'b -> 'a) -> 'a -> 'b t -> 'a
val exists : ('a -> bool) -> 'a t -> bool
val map : ('a -> 'b) -> 'a t -> 'b t
val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
val iter : ('a -> unit) -> 'a t -> unit
val iter2 : ('a -> 'b -> unit) -> 'a t -> 'b t -> unit

val fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a

val to_source : 'a t -> 'a Streaming.Source.t
val sink : unit -> ('a, 'a t option) Streaming.Sink.t

