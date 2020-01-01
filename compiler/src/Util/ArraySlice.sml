structure ArraySlice = struct
    open ArraySlice

    fun uncons vs =
        if length vs > 0
        then SOME (sub (vs, 0), subslice (vs, 1, NONE))
        else NONE
end

