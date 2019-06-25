structure String = struct
    open String

    structure OrdKey = struct
        type ord_key = string
        val compare = compare
    end

    structure SortedMap = BinaryMapFn(OrdKey)
end

