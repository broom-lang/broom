structure Name :> sig
    eqtype t

    val hash: t -> word
    val compare: t * t -> order

    val fromString: string -> t
    val toString: t -> string
    val toDoc: t -> PPrint.t
    val fresh: unit -> t
    val freshen: t -> t

    structure OrdKey : ORD_KEY where type ord_key = t
end = struct
    datatype t = String of string
               | Fresh of int
               | FreshString of string * int

    val hash = fn String s => HashString.hashString s
                | Fresh i => Word.fromInt i
                | FreshString (s, i) => Word.+ (HashString.hashString s, Word.fromInt i)

    val compare = fn (String s, String s') => String.compare (s, s')
                   | (Fresh i, Fresh i') => Int.compare (i, i')
                   | (FreshString (s, i), FreshString (s', i')) =>
                      (case Int.compare (i, i')
                       of EQUAL => String.compare (s, s')
                        | ord => ord)
                   | (String _, Fresh _) => LESS
                   | (Fresh _, String _) => GREATER
                   | (FreshString _, _) => GREATER
                   | (_, FreshString _) => LESS

    val fromString = String

    val toString = fn String s => s
                    | Fresh i => "g__" ^ Int.toString i
                    | FreshString (s, i) => s ^ Int.toString i
    val toDoc = PPrint.text o toString

    local
        val counter = ref 0
        fun next () = let val res = !counter
                      in counter := res + 1
                       ; res
                      end
    in
        fun fresh () = Fresh (next ())

        fun freshen name =
             let val i = next ()
             in case name
                of (String s | FreshString (s, _)) => FreshString (s, i)
                 | Fresh _ => Fresh i
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

