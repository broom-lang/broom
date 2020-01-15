signature HASH_MAP = sig
    type key
    type 'v t

    val empty : 'v t
    val insert : 'v t -> key * 'v -> 'v t
    val update : 'v t -> key -> ('v option -> 'v) -> 'v t
    val find : 'v t -> key -> 'v option
    val lookup : 'v t -> key -> 'v
    val length : 'v t -> int
    val fold : ((key * 'v) * 'a -> 'a) -> 'a -> 'v t -> 'a
    val map : ('v -> 'a) -> 'v t -> 'a t
    val mapi : (key * 'v -> 'a) -> 'v t -> 'a t
    val appi : (key * 'v -> unit) -> 'v t -> unit
    val eq : ('v * 'v -> bool) -> 'v t * 'v t -> bool

    val toString : ('v -> string) -> 'v t -> string
    val inspect : ('v -> string) -> 'v t -> string
end

functor HashMap (Key : sig
    include HASH_KEY
    val toString : hash_key -> string
end) :> HASH_MAP where type key = Key.hash_key = struct
    open Word32
    infix 5 << >>

    type key = Key.hash_key
    val hashVal = fromLargeWord o Word.toLargeWord o Key.hashVal
    val eq = Key.sameKey

    datatype 'v trie
        = Bitmapped of {bitmap : word, nodes : 'v trie vector}
        | Collision of {hash : word, kvs : (key * 'v) vector}
        | Leaf of key * 'v

    type 'v t = {root : 'v trie, len : int}

    val length : 'v t -> int = #len

    val bits = 0w5
    val width = 0w1 << bits
    val mask = width - 0w1

    fun hashPart hash shift = andb (hash >> shift, mask)

    fun bitpos hash shift = 0w1 << Word.fromLargeWord (toLargeWord (hashPart hash shift))

    fun bitindex bitmap bit = toInt (bitCount (andb (bitmap, bit - 0w1)))

    fun isset bitmap bit = andb (bitmap, bit) <> 0w0

    val empty = {root = Bitmapped {bitmap = 0w0, nodes = #[]}, len = 0}

    fun update {root, len} k f = trieUpdate len root 0w0 (hashVal k) k f

    and trieUpdate len trie shift hash k f =
        case trie
        of Bitmapped {bitmap, nodes} =>
            let val bit = bitpos hash shift
                val index = bitindex bitmap bit
            in  if isset bitmap bit
                then let val node = Vector.sub (nodes, index)
                         val {root = node, len} = trieUpdate len node (Word.+ (shift, bits)) hash k f
                     in { root = Bitmapped {bitmap, nodes = Vector.update (nodes, index, node)}
                        , len }
                     end
                else { root = Bitmapped { bitmap = orb (bitmap, bit)
                                        , nodes = VectorExt.pushAt (nodes, index, Leaf (k, f NONE)) }
                     , len = Int.+ (len, 1) }
            end

         | Collision {hash = hash', kvs} =>
            if hash = hash'
            then case Vector.findi (fn (i, (k', _)) => eq (k', k)) kvs
                 of SOME (i, (_, v)) =>
                     { root = Collision {hash = hash', kvs = Vector.update (kvs, i, (k, f (SOME v)))}
                     , len }
                  | NONE =>
                     { root = Collision {hash = hash', kvs = VectorExt.append (kvs, (k, f NONE))}
                     , len = Int.+ (len, 1) }
            else let val node = Bitmapped { bitmap = bitpos hash' shift
                                          , nodes = #[trie] }
                 in trieUpdate len node shift hash k f
                 end

         | Leaf (kv' as (k', v)) =>
            if eq (k, k')
            then {root = Leaf (k, f (SOME v)), len}
            else let val hash' = hashVal k'
                     val node = 
                         if hash = hash'
                         then Collision {hash, kvs = #[kv', (k, f NONE)]}
                         else let val node = Bitmapped {bitmap = 0w0, nodes = #[]}
                                  val node = #root (trieUpdate len node shift hash' k' (Fn.constantly v))
                              in #root (trieUpdate len node shift hash k f)
                              end
                 in {root = node, len = Int.+ (len, 1)}
                 end

    fun insert kvs (k, v) = update kvs k (Fn.constantly v)

    fun find {root, len = _} k = trieFind root 0w0 (hashVal k) k

    and trieFind trie shift hash k =
        case trie
        of Bitmapped {bitmap, nodes} =>
            let val bit = bitpos hash shift
            in if isset bitmap bit
               then let val index = bitindex bitmap bit
                        val node = Vector.sub (nodes, index)
                    in trieFind node (Word.+ (shift, bits)) hash k
                    end
               else NONE
            end

         | Collision {hash = _, kvs} =>
            Option.map #2 (Vector.find (fn (k', _) => eq (k', k)) kvs)

         | Leaf (k', v) =>
            if eq (k', k) then SOME v else NONE

    fun lookup kvs k =
        case find kvs k
        of SOME v => v
         | NONE => raise Subscript

    fun fold f acc {root, len = _} = foldTrie f acc root

    and foldTrie f acc =
        fn Bitmapped {bitmap = _, nodes} =>
            Vector.foldl (fn (trie, acc) => foldTrie f acc trie) acc nodes
         | Collision {hash = _, kvs} => Vector.foldl f acc kvs
         | Leaf kv => f (kv, acc)

    fun map f {root, len} = {root = mapTrie f root, len}

    and mapTrie f =
        fn Bitmapped {bitmap, nodes} =>
            Bitmapped {bitmap, nodes = Vector.map (mapTrie f) nodes}
         | Collision {hash, kvs} =>
            Collision {hash, kvs = Vector.map (Pair.second f) kvs}
         | Leaf (k, v) => Leaf (k, f v)

    fun mapi f {root, len} = {root = mapiTrie f root, len}

    and mapiTrie f =
        fn Bitmapped {bitmap, nodes} =>
            Bitmapped {bitmap, nodes = Vector.map (mapiTrie f) nodes}
         | Collision {hash, kvs} =>
            Collision {hash, kvs = Vector.map (fn kv as (k, _) => (k, f kv)) kvs}
         | Leaf (kv as (k, _)) => Leaf (k, f kv)

    fun appi f {root, len = _} = appiTrie f root

    and appiTrie f =
        fn Bitmapped {bitmap = _, nodes} => Vector.app (appiTrie f) nodes
         | Collision {hash = _, kvs} => Vector.app f kvs
         | Leaf kv => f kv

    exception Abort

    fun eq eqVals (kvs, kvs') =
        (length kvs = length kvs'
         andalso fold (fn ((k, v), _) =>
                           case find kvs' k
                           of SOME v' => if eqVals (v, v') then true else raise Abort
                            | NONE => raise Abort)
                      true kvs)
        handle Abort => false

    fun toString valToString {root, len = _} = "{" ^ trieToString valToString root ^ "}"

    and trieToString valToString =
        fn Bitmapped {bitmap = _, nodes} =>
            (case nodes
             of #[] => ""
              | _ =>
                VectorSlice.foldl (fn (node, acc) =>
                                       acc ^ ", " ^ trieToString valToString node)
                                  (trieToString valToString (Vector.sub (nodes, 0)))
                                  (VectorSlice.slice (nodes, 1, NONE)))
         | Collision {hash = _, kvs} =>
            (case kvs
             of #[] => ""
              | _ =>
                VectorSlice.foldl (fn (kv, acc) => acc ^ ", " ^ kvToString valToString kv)
                                  (kvToString valToString (Vector.sub (kvs, 0)))
                                  (VectorSlice.slice (kvs, 1, NONE)))
         | Leaf kv => kvToString valToString kv

    and kvToString valToString (k, v) = Key.toString k ^ " = " ^ valToString v

    fun inspect valToString {root, len} =
        let fun inspectTrie indent =
                fn Bitmapped {bitmap, nodes} =>
                    indent ^ "- Bitmapped " ^ Word32.toString bitmap ^ "\n"
                    ^ Vector.foldl (fn (node, acc) =>
                                        acc ^ inspectTrie (indent ^ "    ") node)
                                   "" nodes
                 | Collision {hash, kvs} =>
                    indent ^ "- Collision " ^ Word32.toString hash ^ " "
                    ^ VectorExt.inspect (kvToString valToString) kvs ^ "\n"
                 | Leaf kv => indent ^ kvToString valToString kv ^ "\n"
        in "len = " ^ Int.toString len ^ "\n"
         ^ "root =\n" ^ inspectTrie "    " root
        end
end

