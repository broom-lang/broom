(* Persistent Bit-partitioned Vector Trie with tail optimization. *)

signature TRICTOR = sig
    type 'a t
    type index = int

    val empty : unit -> 'a t
    val fromVector : 'a vector -> 'a t
    val append : 'a t -> 'a -> 'a t
    val update : 'a t * index * 'a -> 'a t
    val update' : 'a t * index * ('a -> 'a) -> 'a t

    val length : 'a t -> int
    val find : 'a t -> index -> 'a option
    val sub : 'a t * index -> 'a

    val foldl : ('a * 'b -> 'b) -> 'b -> 'a t -> 'b

    val inspect : ('a -> string) -> 'a t -> string
    val toString : ('a -> string) -> 'a t -> string
end

structure Trictor :> TRICTOR = struct
    open Word32
    infix 5 << >>

    type index = int

    datatype 'a trie
        = Branch of 'a trie vector
        | Leaves of 'a vector

    type 'a t = { root : 'a trie, tail : 'a vector
                , len : word, shift : word }

    val bits = 0w5
    val width = 0w1 << bits
    val mask = width - 0w1

    fun empty () =
        { root = Branch #[], tail = #[]
        , len = 0w0, shift = bits }

    fun tailOffset len =
        if len < width
        then 0w0
        else ((len - 0w1) >> bits) << bits

    fun append (vs as {len, ...}: 'a t) v =
        if len - tailOffset len < width
        then tailPush vs v
        else triePush vs v

    and tailPush ({root, tail, len, shift}: 'a t) v =
        { root, tail = Vector.append (tail, v)
        , len = len + 0w1, shift }

    and triePush ({root, tail, len, shift}: 'a t) v =
        if (len >> bits) > (0w1 << shift)
        then { root = Branch #[root, path tail shift]
             , tail = #[v], len = len + 0w1, shift = shift + bits }
        else { root = pushTail len root shift tail
             , tail = #[v], len = len + 0w1, shift }

    and pushTail len parent level tail =
        case parent
        of Branch nodes =>
            let val j = andb((len - 0w1) >> level, mask)
                val node =
                    if level = bits
                    then Leaves tail
                    else if j < fromInt (Vector.length nodes)
                         then let val child = Vector.sub (nodes, toInt j)
                              in pushTail len child (level - bits) tail
                              end
                         else path tail (level - bits)
            in Branch (Vector.append (nodes, node))
            end
         | Leaves _ => raise Fail "unreachable"

    and path vs level =
        if level = 0w0
        then Leaves vs
        else Branch #[path vs (level - bits)]

    fun update' ({root, tail, len, shift}: 'a t, i, f) =
        let val i = fromInt i
        in  if i >= len
            then raise Subscript
            else if i >= tailOffset len
                 then {root, tail = tailUpdate tail i f, len, shift}
                 else {root = trieUpdate root shift i f, tail, len, shift}
        end

    and tailUpdate tail i f =
        let val j = toInt (andb(i, mask))
        in Vector.update (tail, j, f (Vector.sub (tail, j)))
        end

    and trieUpdate node level i f =
        case node
        of Branch nodes =>
            let val j = toInt (andb(i >> level, mask))
                val node' = trieUpdate (Vector.sub (nodes, j)) (level - bits) i f
            in Branch (Vector.update (nodes, j, node'))
            end
         | Leaves leaves =>
            let val j = toInt (andb(i, mask))
            in Leaves (Vector.update (leaves, j, f (Vector.sub (leaves, j))))
            end

    fun update (vs, i, v) = update' (vs, i, Fn.constantly v)

    fun length ({len, ...}: 'a t) = toInt len

    fun find ({root, tail, len, shift}: 'a t) i =
        let val i = fromInt i
        in  if i >= len
            then NONE
            else SOME (if i >= tailOffset len
                       then tailFind tail i
                       else trieFind root shift i)
        end

    and tailFind tail i = Vector.sub (tail, toInt(andb(i, mask)))

    and trieFind node level i =
        case node
        of Branch nodes =>
            trieFind (Vector.sub (nodes, toInt (andb(i >> level, mask))))
                     (level - bits) i
         | Leaves leaves =>
            Vector.sub (leaves, toInt (andb(i, mask)))

    fun sub (vs, i) =
        case find vs i
        of SOME v => v
         | NONE => raise Subscript

    open Int

    fun foldl f acc ({root, tail, ...}: 'a t) =
        tailFoldl f (trieFoldl f acc root) tail

    and tailFoldl f acc tail = Vector.foldl f acc tail

    and trieFoldl f acc =
        fn Branch nodes =>
            Vector.foldl (fn (node, acc) => trieFoldl f acc node) acc nodes
         | Leaves leaves => Vector.foldl f acc leaves

    fun fromVector vec =
        let val len = Vector.length vec
        in if Vector.length vec <= Word32.toInt width
           then {root = Branch #[], tail = vec, len = Word32.fromInt len, shift = bits}
           else Vector.foldl (fn (v, vs) => append vs v) (empty ()) vec
        end

    fun inspect inspectEl ({root, tail, len, shift}: 'a t) =
        let fun inspectTrie indent =
                fn Branch nodes =>
                    indent ^ "- Branch with " ^ Int.toString (Vector.length nodes) ^ " nodes:\n"
                    ^ Vector.foldl (fn (node, res) =>
                                        res ^ inspectTrie (indent ^ "    ") node)
                                   "" nodes
                 | Leaves leaves =>
                    indent ^ "- Leaves " ^ Vector.inspect inspectEl leaves ^ "\n"
        in "len = " ^ Word32.fmt StringCvt.DEC len ^ "\n"
         ^ "shift = " ^ Word32.fmt StringCvt.DEC shift ^ "\n"
         ^ "root =\n"
         ^ inspectTrie "    " root
         ^ "tail = " ^ Vector.inspect inspectEl tail
        end

    fun toString elToString vs =
        case length vs
        of 0 => "[]"
         | 1 => "[" ^ elToString (sub (vs, 0)) ^ "]"
         | _ => foldl (fn (v, res) => res ^ ", " ^ elToString v)
                      "[" vs ^ "]"
end

