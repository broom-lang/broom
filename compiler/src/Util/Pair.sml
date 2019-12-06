signature PAIR = sig
    include BIMAPPABLE where type ('a, 'b) t = 'a * 'b

    val flip: ('a, 'b) t -> ('b, 'a) t
end

structure Pair :> PAIR = struct
    type ('a, 'b) t = 'a * 'b

    fun bimap f g (a, b) = (f a, g b)
    fun first f (a, b) = (f a, b)
    fun second f (a, b) = (a, f b)
    fun flip (a, b) = (b, a)
end

