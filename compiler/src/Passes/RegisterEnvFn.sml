signature REGISTER_ENV = sig
    structure Abi : ABI
    structure Register : REGISTER where type t = Abi.RegIsa.Register.t

    type t

    val empty : t
    val find : t -> CpsId.t -> Register.t option
    val lookupReg : t -> CpsId.t -> Register.t
    val allocateFixed : t -> CpsId.t -> Register.t -> t

    (* Get the register for the id, first allocating one if necessary: *)
    val findOrAllocate : t -> CpsId.t -> t * Register.t

    val free : t -> CpsId.t -> Register.t -> t
end

functor RegisterEnvFn (Abi : ABI) :> REGISTER_ENV
    where type Abi.RegIsa.Register.t = Abi.RegIsa.Register.t
= struct
    structure Abi = Abi
    structure Register = Abi.RegIsa.Register

    type t = { registers : Register.t CpsId.SortedMap.map
             , stack : int CpsId.SortedMap.map
             , freeRegs : Register.t list }

    val empty =
        { freeRegs = Vector.toList Abi.generalRegs
        , registers = CpsId.SortedMap.empty
        , stack = CpsId.SortedMap.empty }

    fun find ({registers, ...} : t) id = CpsId.SortedMap.find (registers, id)

    fun lookupReg ({registers, ...} : t) id = CpsId.SortedMap.lookup (registers, id)

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
            {freeRegs, registers = CpsId.SortedMap.insert (registers, id, reg), stack}
         | NONE => raise Fail "unimplemented"

    fun findOrAllocate (env as {freeRegs, registers, stack}) id =
        case CpsId.SortedMap.find (registers, id)
        of SOME reg => (env, reg)
         | NONE =>
            (case freeRegs
             of reg :: freeRegs =>
                 ( {freeRegs, registers = CpsId.SortedMap.insert (registers, id, reg), stack}
                 , reg )
              | [] => raise Fail "unimplemented: out of freeRegs")

    fun free {freeRegs, registers, stack} id origReg =
        let val (registers, freeRegs) =
                case CpsId.SortedMap.find (registers, id)
                of SOME reg =>
                    if Register.eq (reg, origReg)
                    then (#1 (CpsId.SortedMap.remove (registers, id)), reg :: freeRegs)
                    else raise Fail "unimplemented"
                 | NONE => raise Fail "unimplemented"
            val stack =
                case CpsId.SortedMap.find (stack, id)
                of SOME i => raise Fail "unimplemented"
                 | NONE => stack
        in {freeRegs, registers, stack}
        end
end

