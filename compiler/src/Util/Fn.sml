signature FN = sig
    val identity: 'a -> 'a
    val constantly: 'a -> 'b -> 'a
end

structure Fn :> FN = struct
    fun identity x = x

    fun constantly x y = x
end

