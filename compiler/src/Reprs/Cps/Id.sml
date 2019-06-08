signature ID = sig
    type t

    val toDoc: t -> PPrint.t

    structure HashKey: HASH_KEY where type hash_key = t
    structure HashSet: HASH_SET where type item = t

    structure OrdKey: ORD_KEY where type ord_key = t
    structure SortedMap: ORD_MAP where type Key.ord_key = t
end

structure Id :> ID = struct
    type t = word

    val toDoc = PPrint.word

    structure HashKey = struct
        type hash_key = t
        val hashVal = Fn.identity
        val sameKey = op=
    end

    structure HashSet = HashSetFn(HashKey)
    
    structure OrdKey = struct
        type ord_key = t
        val compare = Word.compare
    end

    structure SortedMap = BinaryMapFn(OrdKey)
end
