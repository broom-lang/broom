signature FN = sig
    val identity: 'a -> 'a
end

structure Fn :> FN = struct
    fun identity x = x
end

