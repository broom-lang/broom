structure Option = struct
    open Option

    fun mapOr f default = fn SOME v => f v
                           | NONE => default

    fun orElse thunk = fn opt as SOME _ => opt
                        | NONE => thunk ()
end

