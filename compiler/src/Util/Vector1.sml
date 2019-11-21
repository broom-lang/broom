(* Non-empty vector. *)
structure Vector1 :> sig
    type 'a vector
    
    val singleton : 'a -> 'a vector
    val fromVector : 'a Vector.vector -> 'a vector option
    val toVector : 'a vector -> 'a Vector.vector
    val fromList : 'a list -> 'a vector option

    val length : 'a vector -> int
    val sub : 'a vector * int -> 'a
    val foldl : ('a * 'b -> 'b) -> 'b -> 'a vector -> 'b
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a vector -> 'b
    val map : ('a -> 'b) -> 'a vector -> 'b vector
    val app : ('a -> unit) -> 'a vector -> unit
    val exists : ('a -> bool) -> 'a vector -> bool
    val all : ('a -> bool) -> 'a vector -> bool
    val zipWith : ('a * 'b -> 'c) -> 'a vector * 'b vector -> 'c vector
    val zip : 'a vector * 'b vector -> ('a * 'b) vector
    val zip3With : ('a * 'b * 'c -> 'd) -> 'a vector * 'b vector * 'c vector -> 'd vector

    structure Slice : sig
        type 'a slice

        val slice : 'a vector * int * int option -> 'a slice
        val uncons : 'a slice -> ('a * 'a slice) option
        val foldl : ('a * 'b -> 'b) -> 'b -> 'a slice -> 'b
    end
end = struct
    open Vector

    fun singleton v = #[v]

    fun fromVector vec =
        if Vector.length vec > 0
        then SOME vec
        else NONE

    fun toVector vec1 = vec1

    val fromList =
        fn ls as _ :: _ => SOME (Vector.fromList ls)
         | [] => NONE

    fun tabulate (args as (n, _)) =
        if n > 0
        then SOME (Vector.tabulate args)
        else NONE
    
    fun concat vecs =
        case Vector.concat vecs
        of #[] => NONE
         | vec => SOME vec

    structure Slice = VectorSlice
end

type 'a vector1 = 'a Vector1.vector

