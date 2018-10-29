structure Name :> sig
    eqtype t

    val hash: t -> word

    val fromString: string -> t
    val toString: t -> string
end = struct
    datatype t = String of string

    val hash = fn String s => HashString.hashString s

    val fromString = String
    val toString = fn String s => s
end

structure NameHashTable = HashTableFn(type hash_key = Name.t
                                      val hashVal = Name.hash
                                      val sameKey = op=)
