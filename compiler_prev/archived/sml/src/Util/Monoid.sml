infixr 6 <>

signature MONOID = sig
    type t

    val empty: t
    val <> : t * t -> t
end

