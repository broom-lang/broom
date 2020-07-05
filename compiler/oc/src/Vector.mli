(* Immutable array implemented as `'a array`. Like the Vector from the SML
   Basis. Great for short sequences but bad for long ones because the whole vector
   gets copied all the time. *)

type 'a t

val singleton : 'a -> 'a t

val length : 'a t -> int
val get : 'a t -> int -> 'a

val of_list : 'a list -> 'a t
val to_list : 'a t -> 'a list

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
val fold_right : ('b -> 'a -> 'a) -> 'b t -> 'a -> 'a
val for_all : ('a -> bool) -> 'a t -> bool
val exists : ('a -> bool) -> 'a t -> bool
val map : ('a -> 'b) -> 'a t -> 'b t
val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
val iter : ('a -> unit) -> 'a t -> unit
val find_opt : ('a -> bool) -> 'a t -> 'a option
val find : ('a -> bool) -> 'a t -> 'a
val append : 'a t -> 'a t -> 'a t
val split : ('a * 'b) t -> 'a t * 'b t

val fold_left2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a

