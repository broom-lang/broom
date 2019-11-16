(* Persistent Union-Find based on Conchon & Filliatre (2007).
   Extended for unification variables and implemented on `Trictor`. *)

signature UNION_FIND = sig
    type 'a pool
    type 'a t

    val pool : unit -> 'a pool
    val new : 'a pool -> 'a t * 'a pool
    val find : 'a pool -> 'a t -> 'a t
    val get : 'a pool -> 'a t -> ('a t, 'a) Either.t
    val union : 'a pool -> 'a t * 'a t -> 'a pool
    val define : 'a pool -> 'a t -> 'a -> ('a, 'a pool) Either.t
end

structure UnionFind :> UNION_FIND = struct
    type 'a t = int

    datatype 'a node
        = Link of 'a t
        | Leaf of 'a option

    type 'a pool =
        { parents : 'a node Trictor.t ref
        , ranks : int Trictor.t }

    fun pool () = 
        { parents = ref (Trictor.empty ())
        , ranks = Trictor.empty () }

    fun new {parents = ref parents, ranks} =
        ( Trictor.length parents
        , { parents = ref (Trictor.append parents (Leaf NONE))
          , ranks = Trictor.append ranks 0 } )

    fun find {parents, ranks = _} i =
        let fun doFind parents i =
                case Trictor.sub (parents, i)
                of Leaf (SOME v) => (parents, i)
                 | Leaf NONE => (parents, i)
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
           of Leaf (SOME v) => Either.Right v
            | Leaf NONE => Either.Left repr
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

    fun define (pool as {parents, ranks}) i v =
        case get pool i
        of Either.Left i =>
            Either.Right { parents = ref (Trictor.update (!parents, i, Leaf (SOME v)))
                         , ranks }
         | Either.Right v => Either.Left v
end

