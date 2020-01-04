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

    fun pick freeRegs reg =
        let val rec extract =
                fn freeReg :: freeRegs =>
                    if Register.eq (freeReg, reg)
                    then SOME freeRegs
                    else Option.map (fn freeRegs => freeReg :: freeRegs)
                                    (extract freeRegs)
                 | [] => NONE
        in extract freeRegs
        end

    fun allocateFixed {registers, stack, freeRegs} id reg =
        case pick freeRegs reg
        of SOME freeRegs =>
            {freeRegs, registers = Cps.Program.Map.insert registers (id, reg), stack}
         | NONE => raise Fail "unimplemented"

    fun allocate {freeRegs, registers, stack} id =
        case freeRegs
        of reg :: freeRegs =>
            ( {freeRegs, registers = Cps.Program.Map.insert registers (id, reg), stack}
            , reg )
         | [] => raise Fail "unimplemented: out of freeRegs"
end

