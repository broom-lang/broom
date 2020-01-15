signature REGISTER_HINTS = sig
    structure Abi : ABI
    structure Location : LOCATION where type Register.t = Abi.RegIsa.Register.t

    type t
    type counts = (int Location.SortedMap.map) CpsId.SortedMap.map

    val empty : t
    val emptyCounts : counts
    val fromCounts : counts -> t
    val find : t -> CpsId.t -> Location.t list
    val hint : t -> CpsId.t -> Location.t -> t
    val merge : t -> t -> t
    val forgetCallerSaves : t -> t
end

functor RegisterHintsFn (Args : sig
    structure Abi : ABI
    structure Location : LOCATION where type Register.t = Abi.RegIsa.Register.t
end) :> REGISTER_HINTS
    where type Abi.RegIsa.def = Args.Abi.RegIsa.def
    where type Location.t = Args.Location.t
= struct
    structure Abi = Args.Abi
    structure Register = Args.Abi.RegIsa.Register
    structure Location = Args.Location
    structure Map = CpsId.SortedMap

    type reg = Register.t
    datatype location = datatype Location.t

    val op|> = Fn.|>

    type t = location list Map.map
    type counts = (int Location.SortedMap.map) Map.map

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
        in Map.map idHints counts
        end

    fun find hints id = getOpt (Map.find (hints, id), [])

    fun forget hints loc =
        Map.map (List.filter (fn loc' => not (Location.eq (loc', loc)))) hints

    fun hint hints id loc =
        let val hints = forget hints loc
        in Map.insert (hints, id, loc :: find hints id)
        end

    fun forgetCallerSaves hints =
        Vector.foldl (fn (loc, hints) => forget hints loc)
                     hints
                     (Vector.map Register (#callerSaves Abi.foreignCallingConvention))

    fun merge hints hints' =
        Map.unionWith (fn (idHints, idHints') => idHints' @ idHints) (hints, hints')
end

