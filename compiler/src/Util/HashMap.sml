functor HashMap (Key : HASH_KEY) :> sig
    type key = Key.hash_key
    type 'v t

    val empty : 'v t
    val insert : 'v t -> key * 'v -> 'v t
    val find : 'v t -> key -> 'v option
end = struct
    open Word32
    infix 5 << >>

    type key = Key.hash_key
    val hash = Key.hashVal
    val eq = Key.sameKey

    datatype 'v trie
        = Branch of {bitmap : word, nodes : 'v trie vector}
        | Leaves of {bitmap : word, leaves : 'v trie_leaf vector}

    and 'v trie_leaf
        = Collision of {hash : word, kvs : (key * 'v) vector}
        | Leaf of key * 'v

    type 'v t = {root : 'v trie, len : int}

    val bits = 0w5
    val width = 0w1 << bits
    val mask = width - 0w1

    fun hashPart hash shift = andb (hash >> shift, mask)

    fun bitpos hash shift = 0w1 << hashPart hash shift

    fun bitindex bitmap bit = bitCount (andb (bitmap, bit - 0w1))

    fun isset bitmap bit = andb (bitmap, bit) <> 0w0

    val empty = {root = Branch {bitmap = 0w0, nodes = #[]}, len = 0}

    fun insert {root, len} (kv as (k, _)) = trieInsert len root 0w0 (hash k) kv

    and trieInsert len trie shift hash (kv as (k, _)) =
        let val bit = bitpos hash shift
        in  case trie
            of Branch {bitmap, nodes} =>
                let val index = toInt (bitindex bitmap bit)
                    val node = Vector.sub (nodes, index)
                    val {root = node, len} = trieInsert len node (shift + bits) hash kv
                in { root = Branch {bitmap, nodes = Vector.update (nodes, index, node)}
                   , len }
                end
             | Leaves {bitmap, leaves} => 
                let val index = toInt (bitindex bitmap bit)
                in if isset bitmap bit 
                   then case Vector.sub (leaves, index)
                        of node as Collision {hash = hash', kvs} =>
                            if hash = hash'
                            then let val node = 
                                         case Vector.findi (fn (i, (k', v)) => eq (k', k)) kvs
                                         of SOME (i, _) =>
                                             Collision {hash = hash', kvs = Vector.update (kvs, i, kv)}
                                          | NONE =>
                                             Collision {hash = hash', kvs = Vector.append (kvs, kv)}
                                 in { root = Leaves {bitmap, leaves = Vector.update (leaves, index, node)}
                                    , len }
                                 end
                            else let val node = Leaves {bitmap = bitpos hash' shift, leaves = #[node]}
                                 in trieInsert len node shift hash kv
                                 end
                         | Leaf _ =>
                            { root = Leaves {bitmap, leaves = Vector.update (leaves, index, Leaf kv)}
                            , len }
                   else { root = Leaves { bitmap = andb (bitmap, bit)
                                        , leaves = Vector.pushAt (leaves, index, Leaf kv) }
                        , len = Int.+(len, 1) }
                end
        end

    fun find {root, len = _} k = trieFind root 0w0 (hash k) k

    and trieFind trie shift hash k =
        let val bit = bitpos hash shift
        in  case trie
            of Branch {bitmap, nodes} =>
                let val index = toInt (bitindex bitmap bit)
                in if isset bitmap bit
                   then trieFind (Vector.sub (nodes, index)) (shift + bits) hash k
                   else NONE
                end
             | Leaves {bitmap, leaves} =>
                let val index = toInt (bitindex bitmap bit)
                in if isset bitmap bit
                   then case Vector.sub (leaves, index)
                        of Collision {hash = _, kvs} =>
                            Option.map #2 (Vector.find (fn (k', _) => eq (k', k)) kvs)
                         | Leaf (k, v) => SOME v
                   else NONE
                end
        end
end

