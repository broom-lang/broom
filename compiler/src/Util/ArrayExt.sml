structure ArrayExt = struct
    open Array

    fun stableSort cmp arr = ArraySliceExt.stableSort cmp (ArraySlice.full arr)
end

