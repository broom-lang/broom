signature REGISTER_ENV = sig
    structure Abi : ABI
    structure Register : REGISTER where type t = Abi.RegIsa.Register.t

    type builder = Abi.RegIsa.Program.Builder.builder

    type t

    val empty : t
    val find : t -> CpsId.t -> Register.t option
    val lookupReg : t -> CpsId.t -> Register.t
    val allocateFixed : t -> CpsId.t -> Register.t -> t

    (* Get the register for the id, first allocating one if necessary: *)
    val findOrAllocate : t -> CpsId.t -> t * Register.t

    (* Free registers and stack slots of the id, ensuring it is in the reg: *)
    val freeIn : t -> builder -> Label.t -> CpsId.t -> Register.t -> t

    (* Free registers and stack slots of the id: *)
    val free : t -> CpsId.t -> t

    (* Move values from caller-save to callee-save registers or stack slots: *)
    val evacuateCallerSaves : t -> builder -> Label.t -> t
end

functor RegisterEnvFn (Abi : ABI) :> REGISTER_ENV
    where type Abi.RegIsa.Register.t = Abi.RegIsa.Register.t
    where type Abi.RegIsa.Program.Builder.builder = Abi.RegIsa.Program.Builder.builder
= struct
    structure Abi = Abi
    structure Register = Abi.RegIsa.Register
    structure Stmt = Abi.RegIsa.Stmt
    structure Builder = Abi.RegIsa.Program.Builder

    type builder = Builder.builder

    type t = { registers : Register.t CpsId.SortedMap.map
             , stack : int CpsId.SortedMap.map
             , freeRegs : Register.t list }

    val empty =
        { freeRegs = Vector.toList Abi.generalRegs
        , registers = CpsId.SortedMap.empty
        , stack = CpsId.SortedMap.empty }

    fun find ({registers, ...} : t) id = CpsId.SortedMap.find (registers, id)

    fun lookupReg ({registers, ...} : t) id = CpsId.SortedMap.lookup (registers, id)

    fun pick pred freeRegs =
        let val rec extract =
                fn freeReg :: freeRegs =>
                    if pred freeReg
                    then SOME (freeRegs, freeReg)
                    else Option.map (fn (freeRegs, reg) => (freeReg :: freeRegs, reg))
                                    (extract freeRegs)
                 | [] => NONE
        in extract freeRegs
        end

    fun pickEq freeRegs reg =
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
        case pickEq freeRegs reg
        of SOME freeRegs =>
            {freeRegs, registers = CpsId.SortedMap.insert (registers, id, reg), stack}
         | NONE => raise Fail "unimplemented: "

    fun findOrAllocate (env as {freeRegs, registers, stack}) id =
        case CpsId.SortedMap.find (registers, id)
        of SOME reg => (env, reg)
         | NONE =>
            (case freeRegs
             of reg :: freeRegs =>
                 ( {freeRegs, registers = CpsId.SortedMap.insert (registers, id, reg), stack}
                 , reg )
              | [] => raise Fail "unimplemented: out of freeRegs")

    fun free {freeRegs, registers, stack} id =
        let val (registers, freeRegs) =
                case CpsId.SortedMap.find (registers, id)
                of SOME reg =>
                    (#1 (CpsId.SortedMap.remove (registers, id)), reg :: freeRegs)
                 | NONE => (registers, freeRegs)
            val stack =
                case CpsId.SortedMap.find (stack, id)
                of SOME i => raise Fail "unimplemented"
                 | NONE => stack
        in {freeRegs, registers, stack}
        end

    fun freeIn (env as {registers, ...} : t) builder label id reg =
        case CpsId.SortedMap.find (registers, id)
        of SOME reg' =>
            let val env =
                    if not (Register.eq (reg', reg))
                    then let val env = free env id
                             val env = allocateFixed env id reg
                             do Builder.insertStmt builder label (Stmt.Def (reg', Abi.RegIsa.Instrs.Oper.move reg))
                         in env
                         end
                    else env
            in free env id
            end
         | NONE => raise Fail "unimplemented"

    fun evacuateCallerSaves (env as {registers, ...} : t) builder label =
        let fun step (id, reg, {freeRegs, registers, stack}) =
                if Abi.CallingConvention.isCallerSave Abi.foreignCallingConvention reg
                then case pick (Abi.CallingConvention.isCalleeSave Abi.foreignCallingConvention) freeRegs
                     of SOME (freeRegs, reg') =>
                         ( Builder.insertStmt builder label (Stmt.Def (reg, Abi.RegIsa.Instrs.Oper.move reg'))
                         ; { freeRegs = reg :: freeRegs
                           , registers = CpsId.SortedMap.insert (registers, id, reg')
                           , stack } )
                      | NONE => raise Fail "unimplemented"
                else env
        in CpsId.SortedMap.foldli step env registers
        end
end

