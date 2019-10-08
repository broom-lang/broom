signature FN = sig
    val identity : 'a -> 'a
    val constantly : 'a -> 'b -> 'a
    val |> : 'a * ('a -> 'b) -> 'b
end

structure Fn :> FN = struct
    fun identity x = x

    fun constantly x _ = x

    fun |> (x, f) = f x
end

infix 2 o
infix 0 :=
infix 1 |>

