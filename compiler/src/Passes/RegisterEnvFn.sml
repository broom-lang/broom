signature REGISTER_ENV = sig
    structure Abi : ABI
    structure Register : REGISTER where type t = Abi.RegIsa.Register.t

    type builder = Abi.RegIsa.Program.Builder.builder

    type t

    val empty : t
    val find : t -> CpsId.t -> Register.t option
    val lookupReg : t -> CpsId.t -> Register.t
    val allocateFixed : t -> builder -> Label.t -> CpsId.t -> Register.t -> t

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

    val op|> = Fn.|>

    structure Slots :> sig
        type t

        val empty : t
        val next : t -> t * int
        val free : t -> int -> t
    end = struct
        type t = {slots : int list, len : int}

        val empty = {slots = [], len = 0}

        fun next {slots, len} =
            case slots
            of slot :: slots => ({slots, len}, slot)
             | [] => ({slots, len = len + 1}, len)

        fun free {slots, len} slot = {slots = slot :: slots, len}
    end

    type t = { registers : Register.t CpsId.SortedMap.map
             , freeRegs : Register.t list
             , stack : int CpsId.SortedMap.map
             , freeSlots : Slots.t }

    val empty =
        { freeRegs = Vector.toList Abi.generalRegs
        , registers = CpsId.SortedMap.empty
        , stack = CpsId.SortedMap.empty
        , freeSlots = Slots.empty }

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

    fun free {freeRegs, registers, stack, freeSlots} id =
        let val (registers, freeRegs) =
                case CpsId.SortedMap.find (registers, id)
                of SOME reg =>
                    (#1 (CpsId.SortedMap.remove (registers, id)), reg :: freeRegs)
                 | NONE => (registers, freeRegs)
            val stack =
                case CpsId.SortedMap.find (stack, id)
                of SOME i => raise Fail "unimplemented"
                 | NONE => stack
        in {freeRegs, registers, stack, freeSlots}
        end

    fun stackAllocate {stack, freeSlots, registers, freeRegs} id =
        let val (freeSlots, sloti) = Slots.next freeSlots
        in ({stack, freeSlots, registers, freeRegs}, sloti)
        end

    fun unspill (env as {stack, ...} : t) builder label id reg =
        case CpsId.SortedMap.find (stack, id)
        of SOME _ => env
         | NONE =>
            let val env = free env id
                val (env, sloti) = stackAllocate env id
            in Builder.insertStmt builder label (Stmt.Def (reg, Abi.RegIsa.Instrs.Oper.stackLoad Abi.sp sloti))
             ; env
            end

    fun evacuate {registers, stack, freeRegs, freeSlots} builder label reg =
        let val id = CpsId.SortedMap.filter (fn reg' => Register.eq (reg', reg)) registers (* HACK *)
                   |> CpsId.SortedMap.firsti |> valOf |> #1
        in  case pick (fn reg' => not (Register.eq (reg', reg))) freeRegs
            of SOME (freeRegs, reg') =>
                ( Builder.insertStmt builder label (Stmt.Def (reg, Abi.RegIsa.Instrs.Oper.move reg'))
                ; { freeRegs = reg :: freeRegs
                  , registers = CpsId.SortedMap.insert (registers, id, reg')
                  , stack, freeSlots } )
             | NONE => raise Fail "unimplemented"
        end

    fun allocateFixed (env as {registers, stack, freeRegs, freeSlots}) builder label id reg =
        case pickEq freeRegs reg
        of SOME freeRegs =>
            {freeRegs, registers = CpsId.SortedMap.insert (registers, id, reg), stack, freeSlots}
         | NONE =>
            let val env = evacuate env builder label reg
            in allocateFixed env builder label id reg
            end

    fun findOrAllocate (env as {freeRegs, registers, stack, freeSlots}) id =
        case CpsId.SortedMap.find (registers, id)
        of SOME reg => (env, reg)
         | NONE =>
            (case freeRegs
             of reg :: freeRegs =>
                 ( {freeRegs, registers = CpsId.SortedMap.insert (registers, id, reg), stack, freeSlots}
                 , reg )
              | [] => raise Fail "unimplemented: out of freeRegs")

    fun freeIn (env as {registers, ...} : t) builder label id reg =
        case CpsId.SortedMap.find (registers, id)
        of SOME reg' =>
            let val env =
                    if not (Register.eq (reg', reg))
                    then let val env = free env id
                             val env = allocateFixed env builder label id reg
                             do Builder.insertStmt builder label (Stmt.Def (reg', Abi.RegIsa.Instrs.Oper.move reg))
                         in env
                         end
                    else env
            in free env id
            end
         | NONE => raise Fail "unimplemented"

    fun evacuateCallerSaves (env as {registers, ...} : t) builder label =
        let fun step (id, reg, {freeRegs, registers, stack, freeSlots}) =
                if Abi.CallingConvention.isCallerSave Abi.foreignCallingConvention reg
                then case pick (Abi.CallingConvention.isCalleeSave Abi.foreignCallingConvention) freeRegs
                     of SOME (freeRegs, reg') =>
                         ( Builder.insertStmt builder label (Stmt.Def (reg, Abi.RegIsa.Instrs.Oper.move reg'))
                         ; { freeRegs = reg :: freeRegs
                           , registers = CpsId.SortedMap.insert (registers, id, reg')
                           , stack, freeSlots } )
                      | NONE => unspill env builder label id reg
                else env
        in CpsId.SortedMap.foldli step env registers
        end
end

