type 'a t

val singleton : 'a -> 'a t

val get : 'a t -> int -> 'a

val to_vector : 'a t -> 'a Vector.t
val of_vector : 'a Vector.t -> 'a t option
val of_list : 'a list -> 'a t option
val to_list : 'a t -> 'a list

val append : 'a t -> 'a t -> 'a t

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val for_all : ('a -> bool) -> 'a t -> bool
val exists : ('a -> bool) -> 'a t -> bool
val map : ('a -> 'b) -> 'a t -> 'b t
val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
val iter : ('a -> unit) -> 'a t -> unit

val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a

