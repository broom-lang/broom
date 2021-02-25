signature BIMAPPABLE = sig
    type ('a, 'b) t

    val bimap: ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) t -> ('c, 'd) t
    val first: ('a -> 'c) -> ('a, 'b) t -> ('c, 'b) t
    val second: ('b -> 'c) -> ('a, 'b) t -> ('a, 'c) t
end
