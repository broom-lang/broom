structure Option = struct
    open Option

    fun unwrapOrElse opt thunk = case opt
                                 of SOME v => v
                                  | NONE => thunk ()

    fun mapOr f default = fn SOME v => f v
                           | NONE => default

    fun toString contentToString = mapOr contentToString ""
end

