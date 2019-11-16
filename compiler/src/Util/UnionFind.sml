(* Persistent Union-Find based on Conchon & Filliatre (2007).
   Extended for unification variables and implemented on `Trictor`. *)

signature UNION_FIND = sig
    type ('s, 'd) pool
    type ('s, 'd) t

    val pool : unit -> ('s, 'd) pool
    val new : ('s, 'd) pool -> 's -> ('s, 'd) t * ('s, 'd) pool
    val find : ('s, 'd) pool -> ('s, 'd) t -> ('s, 'd) t
    val get : ('s, 'd) pool -> ('s, 'd) t -> 's * (('s, 'd) t, 'd) Either.t
    val union : ('s, 'd) pool -> ('s, 'd) t * ('s, 'd) t -> ('s, 'd) pool
    val define : ('s, 'd) pool -> ('s, 'd) t -> 'd -> ('d, ('s, 'd) pool) Either.t
end

structure UnionFind :> UNION_FIND = struct
    type ('s, 'd) t = int

    datatype ('s, 'd) node
        = Link of ('s, 'd) t
        | Leaf of 's * 'd option

    type ('s, 'd) pool =
        { parents : ('s, 'd) node Trictor.t ref
        , ranks : int Trictor.t }

    fun pool () = 
        { parents = ref (Trictor.empty ())
        , ranks = Trictor.empty () }

    fun new {parents = ref parents, ranks} s =
        ( Trictor.length parents
        , { parents = ref (Trictor.append parents (Leaf (s, NONE)))
          , ranks = Trictor.append ranks 0 } )

    fun find {parents, ranks = _} i =
        let fun doFind parents i =
                case Trictor.sub (parents, i)
                of Leaf (_, SOME _) => (parents, i)
                 | Leaf (_, NONE) => (parents, i)
                 | Link i' =>
                    let val (parents, repr) = doFind parents i'
                    in ( Trictor.update (parents, i, Link repr)
                       , repr )
                    end
            
            val (parents', repr) = doFind (!parents) i
        in parents := parents'
         ; repr
        end

    fun get (pool as {parents, ...}) i =
        let val repr = find pool i
        in case Trictor.sub (!parents, repr)
           of Leaf (s, SOME d) => (s, Either.Right d)
            | Leaf (s, NONE) => (s, Either.Left repr)
            | Link _ => raise Fail "unreachable"
        end

    fun union (pool as {parents = ref parents, ranks}) (i, i') =
        let val repr = find pool i
            val repr' = find pool i'
        in  if repr = repr'
            then pool
            else case Int.compare (Trictor.sub (ranks, repr), Trictor.sub (ranks, repr'))
                 of LESS =>
                    {parents = ref (Trictor.update (parents, repr, Link repr')), ranks}
                  | GREATER =>
                    {parents = ref (Trictor.update (parents, repr', Link repr)), ranks}
                  | EQUAL =>
                    { parents = ref (Trictor.update (parents, repr', Link repr))
                    , ranks = Trictor.update' (ranks, repr, fn rank => rank + 1) }
        end

    fun define (pool as {parents, ranks}) i d =
        case get pool i
        of (s, Either.Left i) =>
            Either.Right { parents = ref (Trictor.update (!parents, i, Leaf (s, SOME d)))
                         , ranks }
         | (_, Either.Right v) => Either.Left v
end

