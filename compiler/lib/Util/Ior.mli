type ('l, 'r) t = 
    | Left of 'l
    | Right of 'r
    | Both of 'l * 'r

val bimap : ('l -> 'a) -> ('r -> 'b) -> ('l, 'r) t -> ('a, 'b) t
val map : ('a -> 'b) -> ('a, 'a) t -> ('b, 'b) t
val biter : ('l -> unit) -> ('r -> unit) -> ('l, 'r) t -> unit

