signature REGISTER_HINTS = sig
    structure Location : LOCATION
    structure Abi : ABI
        where type RegIsa.def = Location.Register.t
        where type RegIsa.loc = Location.t

    type t
    type counts = (Abi.Isa.Type.t * int Location.SortedMap.map) CpsId.SortedMap.map

    val empty : t
    val emptyCounts : counts
    val fromCounts : counts -> t
    val find : t -> CpsId.t -> Abi.Isa.Type.t * Location.t list
    val hint : t -> CpsId.t -> Abi.Isa.Type.t -> Location.t option -> t
    val merge : t -> t -> t
    val forgetCallerSaves : t -> t
end

functor RegisterHintsFn (Args : sig
    structure Location : LOCATION
    structure Abi : ABI
        where type RegIsa.def = Location.Register.t
        where type RegIsa.loc = Location.t
end) :> REGISTER_HINTS
    where type Location.Register.t = Args.Location.Register.t
    where type Location.t = Args.Location.t
= struct
    structure Abi = Args.Abi
    structure Location = Args.Location
    structure Map = CpsId.SortedMap

    datatype location = datatype Location.t

    val op|> = Fn.|>

    type t = (Abi.Isa.Type.t * location list) Map.map
    type counts = (Abi.Isa.Type.t * int Location.SortedMap.map) Map.map

    val empty = Map.empty

    val emptyCounts = Map.empty

    val compareCountedLocs =
        fn ((Register _, n), (Register _, n')) => Int.compare (n, n')
         | ((Register _, _), (StackSlot _, _)) => LESS
         | ((StackSlot _, _), (Register _, _)) => GREATER
         | ((StackSlot _, n), (StackSlot _, n')) => Int.compare (n, n')

    fun fromCounts counts =
        let fun idHints idCounts = idCounts
                |> Location.SortedMap.listItemsi |> Vector.fromList
                |> VectorExt.sort compareCountedLocs
                |> Vector.map #1 |> VectorExt.toList
        in Map.map (Pair.second idHints) counts
        end

    fun find hints id = Map.lookup (hints, id)

    fun forget hints loc =
        Map.map (Pair.second (List.filter (fn loc' => not (Location.eq (loc', loc))))) hints

    fun hint hints id t loc =
        let val hints =
                case loc
                of SOME loc => forget hints loc
                 | NONE => hints
            val idHints =
                case Map.find (hints, id)
                of SOME (_, idHints) =>
                    (case loc
                     of SOME loc => loc :: idHints
                      | NONE => idHints)
                 | NONE =>
                    (case loc
                     of SOME loc => [loc]
                      | NONE => [])
        in Map.insert (hints, id, (t, idHints))
        end

    fun forgetCallerSaves hints =
        Vector.foldl (fn (loc, hints) => forget hints loc)
                     hints
                     (Vector.map Register (#callerSaves Abi.foreignCallingConvention))

    fun merge hints hints' =
        Map.unionWith (fn ((_, idHints), (t, idHints')) => (t, idHints' @ idHints)) (hints, hints')
end

