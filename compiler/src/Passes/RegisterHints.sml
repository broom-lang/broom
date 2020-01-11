signature REGISTER_HINTS = sig
    structure Abi : ABI

    type reg = Abi.RegIsa.Register.t

    type t

    val empty : t
    val find : t -> CpsId.t -> reg list
    val hint : t -> CpsId.t -> reg -> t
    val forgetCallerSaves : t -> t
end

functor RegisterHintsFn (Abi : ABI) :> REGISTER_HINTS
    where type Abi.RegIsa.def = Abi.RegIsa.def
= struct
    structure Abi = Abi
    structure Register = Abi.RegIsa.Register
    structure Map = CpsId.SortedMap

    type reg = Register.t

    type t = reg list Map.map

    val empty = Map.empty

    fun find hints id = getOpt (Map.find (hints, id), [])

    fun forget hints reg =
        Map.map (List.filter (fn reg' => not (Register.eq (reg', reg)))) hints

    fun hint hints id reg =
        let val hints = forget hints reg
        in Map.insert (hints, id, reg :: find hints id)
        end

    fun forgetCallerSaves hints =
        Vector.foldl (fn (reg, hints) => forget hints reg)
                     hints (#callerSaves Abi.foreignCallingConvention)
end

