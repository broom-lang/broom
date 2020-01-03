signature ID = sig
    eqtype t

    val fresh: unit -> t
    val hash: t -> word
    val eq : t * t -> bool
    val compare: t * t -> order
    val toString: t -> string
    val toDoc : t -> PPrint.t

    structure HashKey: HASH_KEY where type hash_key = t
    structure OrdKey: ORD_KEY where type ord_key = t

    structure HashTable: MONO_HASH_TABLE where type Key.hash_key = t
    structure SortedMap: sig
        include ORD_MAP where type Key.ord_key = t
        
        val fromVector: (Key.ord_key * 'v) vector -> 'v map
    end
end

functor Id(UnitStruct: sig end) :> ID = struct
    type t = word

    local val counter = ref 0w0
    in fun fresh () = let val res = !counter
                      in counter := res + 0w1
                       ; res
                      end
    end

    val hash = Fn.identity

    val eq = op=
    
    val compare = Word.compare

    val toString = Int.toString o Word.toInt

    val toDoc = PPrint.text o toString

    structure HashKey = struct
        type hash_key = t

        val hashVal = hash
        val sameKey = op=
    end

    structure OrdKey = struct
        type ord_key = t

        val compare = compare
    end

    structure HashTable = HashTableFn(HashKey)
    
    structure SortedMap = struct
        structure Super = BinaryMapFn(OrdKey)
        open Super

        fun fromVector kvs =
            Vector.foldl (fn ((k, v), map) => insert (map, k, v))
                         empty kvs
    end
end

