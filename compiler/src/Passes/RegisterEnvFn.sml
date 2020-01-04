signature REGISTER_ENV = sig
    structure Abi : ABI

    type t

    val empty : t
    val find : t -> CpsId.t -> Abi.RegIsa.Register.t option
    val lookupReg : t -> CpsId.t -> Abi.RegIsa.Register.t
    val allocateFixed : t -> CpsId.t -> Abi.RegIsa.Register.t -> t
    val allocate : t -> CpsId.t -> t * Abi.RegIsa.Register.t
end

functor RegisterEnvFn (Abi : ABI) :> REGISTER_ENV
    where type Abi.RegIsa.Register.t = Abi.RegIsa.Register.t
= struct
    structure Abi = Abi
    structure Register = Abi.RegIsa.Register

    type t = { registers : Register.t Cps.Program.Map.t
             , stack : int Cps.Program.Map.t
             , freeRegs : Register.t list }

    val empty =
        { freeRegs = Vector.toList Abi.generalRegs
        , registers = Cps.Program.Map.empty
        , stack = Cps.Program.Map.empty }

    fun find ({registers, ...} : t) id = Cps.Program.Map.find registers id

    fun lookupReg ({registers, ...} : t) id = Cps.Program.Map.lookup registers id

    fun allocateFixed {registers, stack, freeRegs} id reg =
        { freeRegs = List.filter (fn reg' => not (Register.eq (reg', reg))) freeRegs
        , registers = Cps.Program.Map.insert registers (id, reg)
        , stack }

    fun allocate (env as {freeRegs, ...} : t) id =
        case freeRegs
        of reg :: freeRegs => (allocateFixed env id reg, reg)
         | [] => raise Fail "unimplemented: out of freeRegs"
end

