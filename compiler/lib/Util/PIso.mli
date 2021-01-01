type ('a, 'b) t

val apply : ('a, 'b) t -> 'a -> 'b option
val unapply : ('a, 'b) t -> 'b -> 'a option

val piso : ('a -> 'b option) -> ('b -> 'a option) -> ('a, 'b) t

val inv : ('a, 'b) t -> ('b, 'a) t
val comp : ('b, 'c) t -> ('a, 'b) t -> ('a, 'c) t

val id : ('a, 'a) t
val unit : ('a, 'a * unit) t
val element : 'a -> (unit, 'a) t
val subset : ('a -> bool) -> ('a, 'a) t

val some : ('a, 'a option) t
val none : (unit, 'a option) t

val cons : ('a * 'a list, 'a list) t
val nil : (unit, 'a list) t

