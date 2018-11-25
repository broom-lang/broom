structure Name :> sig
    eqtype t

    val hash: t -> word
    val compare: t * t -> order

    val fromString: string -> t
    val toString: t -> string
    val fresh: unit -> t

    structure OrdKey : ORD_KEY where type ord_key = t
end = struct
    datatype t = String of string
               | Fresh of int

    val hash = fn String s => HashString.hashString s
                | Fresh i => Word.fromInt i

    val compare = fn (String s, String s') => String.compare (s, s')
                   | (Fresh i, Fresh i') => Int.compare (i, i')
                   | (String _, Fresh _) => LESS
                   | (Fresh _, String _) => GREATER

    val fromString = String

    val toString = fn String s => s
                    | Fresh i => "g__" ^ Int.toString i

    local
        val counter = ref 0
    in
        fun fresh () = let val i = !counter
                       in counter := i + 1
                        ; Fresh i
                       end
    end

    structure OrdKey = struct
        type ord_key = t
        val compare = compare
    end
end

structure NameHashTable = HashTableFn(type hash_key = Name.t
                                      val hashVal = Name.hash
                                      val sameKey = op=)

structure NameSortedMap = BinaryMapFn(Name.OrdKey)

structure NameSortedSet = BinarySetFn(Name.OrdKey)
