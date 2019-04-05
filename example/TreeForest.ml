structure Tree :> sig
    type 'a tree

    val map: ('a -> 'b) -> 'a tree -> 'b tree
end = struct
    datatype 'a tree = Branch of 'a Forest.forest
                     | Leaf of 'a

    fun map f =
        fn Branch forest => Branch (Forest.map f forest)
         | Leaf v => Leaf (f v)
end

structure Forest :> sig
    type 'a forest

    val map: ('a -> 'b) -> 'a forest -> 'b forest
end = struct
    type 'a forest = 'a Tree.tree list

    fun map f trees = List.map (Tree.map f) trees
end

