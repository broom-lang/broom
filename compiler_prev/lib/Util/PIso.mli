type ('a, 'b) t

val apply : ('a, 'b) t -> 'a -> 'b option
val unapply : ('a, 'b) t -> 'b -> 'a option

val piso : ('a -> 'b option) -> ('b -> 'a option) -> ('a, 'b) t
val iso : ('a -> 'b) -> ('b -> 'a) -> ('a, 'b) t
val prism : ('a -> 'b) -> ('b -> 'a option) -> ('a, 'b) t

val inv : ('a, 'b) t -> ('b, 'a) t
val comp : ('b, 'c) t -> ('a, 'b) t -> ('a, 'c) t

val id : ('a, 'a) t
val unit : ('a, 'a * unit) t
val element : 'a -> (unit, 'a) t
val map_snd : ('a, 'b) t -> ('c * 'a, 'c * 'b) t
val subset : ('a -> bool) -> ('a, 'a) t

val fold_left : (('a * 'b), 'a) t -> (('a * 'b list), 'a) t

val some : ('a, 'a option) t
val none : (unit, 'a option) t

val cons : ('a * 'a list, 'a list) t
val nil : (unit, 'a list) t

val opt_non_empty_list : ('a list option, 'a list) t

val vector : ('a list, 'a Vector.t) t
val string : (char list, string) t

