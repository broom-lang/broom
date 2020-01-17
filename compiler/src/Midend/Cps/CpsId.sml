structure CpsId = struct
    structure Super = Id(struct end)
    open Super

    fun toDoc id = PPrint.<> (PPrint.text "%", Super.toDoc id)
    
    structure SortedSet = BinarySetFn(OrdKey)
    structure HashSetMut = HashSetFn(HashKey)
end

