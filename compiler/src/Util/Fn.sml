signature FN = sig
    val identity: 'a -> 'a
    val constantly: 'a -> 'b -> 'a

    val curry: ('a * 'b -> 'c) -> 'a -> 'b -> 'c
end

structure Fn :> FN = struct
    fun identity x = x

    fun constantly x y = x

    fun curry f x y = f (x, y)
end

