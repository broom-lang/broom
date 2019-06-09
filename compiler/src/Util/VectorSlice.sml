structure VectorSlice = struct
    open VectorSlice

    fun uncons slice =
        case length slice 
        of 0 => NONE
         | _ => SOME (sub (slice, 0), subslice (slice, 1, NONE))
end

