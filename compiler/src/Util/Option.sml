structure Option = struct
    open Option

    fun mapOr f default = fn SOME v => f v
                           | NONE => default
end

