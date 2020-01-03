signature REGISTER_ENV = sig
    structure Abi : ABI

    type t

    val empty : t
    val lookupReg : t -> CpsId.t -> Abi.RegIsa.Register.t
    val insertReg : t -> CpsId.t -> Abi.RegIsa.Register.t -> t
    val allocateReg : t -> CpsId.t -> (t * Abi.RegIsa.Register.t) option
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

    fun lookupReg ({registers, ...} : t) id = Cps.Program.Map.lookup registers id

    fun insertReg {registers, stack, freeRegs} id reg =
        { freeRegs = List.filter (fn reg' => not (Register.eq (reg', reg))) freeRegs
        , registers = Cps.Program.Map.insert registers (id, reg)
        , stack }

    fun allocateReg (env as {freeRegs, ...} : t) id =
        case freeRegs
        of reg :: freeRegs => SOME (insertReg env id reg, reg)
         | [] => raise Fail "unimplemented: out of freeRegs"
end

