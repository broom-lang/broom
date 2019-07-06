structure VectorSlice = struct
    open VectorSlice

    fun uncons xs =
        if length xs > 0
        then SOME (sub (xs, 0), subslice (xs, 1, NONE))
        else NONE
end

