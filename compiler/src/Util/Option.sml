structure Option = struct
    open Option

    fun mapOr f default = fn SOME v => f v
                           | NONE => default

    fun orElse thunk = fn opt as SOME _ => opt
                        | NONE => thunk ()

    fun unwrapOrElse thunk =
        fn SOME v => v
         | NONE => thunk ()
end

