structure Pair :> BIMAPPABLE where type ('a, 'b) t = 'a * 'b = struct
    type ('a, 'b) t = 'a * 'b

    fun bimap f g (a, b) = (f a, g b)
    fun first f (a, b) = (f a, b)
    fun second f (a, b) = (a, f b)
end

