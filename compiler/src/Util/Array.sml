structure Array = struct
    open Array

    fun stableSort cmp arr = ArraySlice.stableSort cmp (ArraySlice.full arr)
end

