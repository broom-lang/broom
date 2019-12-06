structure Option = struct
    open Option

    fun unwrapOrElse opt thunk = case opt
                                 of SOME v => v
                                  | NONE => thunk ()

    fun mapOr f default = fn SOME v => f v
                           | NONE => default

    fun orElse thunk = fn opt as SOME _ => opt
                        | NONE => thunk ()
end

