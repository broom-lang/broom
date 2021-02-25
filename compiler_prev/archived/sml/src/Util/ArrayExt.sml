structure ArrayExt = struct
    open Array

    val sort = ArrayQSort.sort

    fun stableSort cmp arr = ArraySliceExt.stableSort cmp (ArraySlice.full arr)
end

