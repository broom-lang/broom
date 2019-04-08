structure Tree :> sig
    type 'a tree

    val singleton: 'a -> 'a tree
    val push: 'a tree -> 'a -> 'a tree
end = struct
    datatype 'a tree = Branch of 'a Forest.forest
                     | Leaf of 'a

    val singleton = Leaf

    fun push tree v =
        let val vtree = singleton v
        in case tree
           of Branch forest => Forest.push forest vtree
            | Leaf _ => Forest.push (Forest.push Forest.empty tree) vtree
        end
end

structure Forest :> sig
    type 'a forest

    val empty: 'a forest
    val push: 'a forest -> 'a tree -> 'a forest
end = struct
    type 'a forest = 'a Tree.tree list

    val empty = []

    fun push forest tree = tree :: forest
end

