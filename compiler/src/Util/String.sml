structure String = struct
    open String

    structure OrdKey = struct
        type ord_key = string
        val compare = compare
    end

    structure SortedMap = BinaryMapFn(OrdKey)

    structure HashKey = struct
        type hash_key = string
        val hashVal = HashString.hashString
        val sameKey = op=
    end

    structure HashTable = HashTableFn(HashKey)
end

