signature REGISTER_ENV = sig
    structure Abi : ABI
    structure Register : REGISTER where type t = Abi.RegIsa.Register.t
    structure Hints : REGISTER_HINTS
    structure Location : LOCATION where type t = Hints.Location.t

    type hints = Hints.t
    type builder = Abi.RegIsa.Program.Builder.builder

    type t

    val empty : int ref -> t

    (* Use in some register.
       Allocates a register for the id if it does not have any.
       Returns the register for the definition site. *)
    val regUse : t -> hints -> builder -> Label.t -> CpsId.t -> t * Register.t

    (* Use in the given register.
       Arranges for the id to be (also) in the given register if not already. *)
    val fixedRegUse : t -> hints -> builder -> Label.t -> CpsId.t -> Register.t -> t

    val fixedUse : t -> hints -> builder -> Label.t -> CpsId.t -> Location.t -> t

    (* Definition in some register.
       If the id is in multiple locations, inserts moves and loads to account for them.
       Allocates a register for the id if it does not have any.
       Finally frees the locations used by the id.
       Returns the register for the use site. *)
    val regDef : t -> hints -> builder -> Label.t -> CpsId.t -> t * Register.t

    (* Use in the given register.
       Arranges for the id to be (also) in the given register if not already. *)
    val fixedRegDef : t -> hints -> builder -> Label.t -> CpsId.t -> Register.t -> t

    val fixedDef : t -> hints -> builder -> Label.t -> CpsId.t -> Location.t -> t

    (* Move id:s away from caller-save registers (except the return value registers). *)
    val evacuateCallerSaves : t -> builder -> Label.t -> t

    (* Emit moves, loads and stores that change env to env'. *)
    val conform : t -> hints -> builder -> Label.t -> t -> unit

    val incCounts : Hints.counts -> t -> Hints.counts

    val fromCounts : int ref -> Hints.counts -> t
end

functor RegisterEnvFn (Args : sig
    structure Hints : REGISTER_HINTS
    structure Abi : ABI
        where type RegIsa.def = Hints.Location.Register.t
        where type RegIsa.loc = Hints.Location.t
end) :> REGISTER_ENV
    where type Abi.RegIsa.def = Args.Abi.RegIsa.def
    where type Abi.RegIsa.loc = Args.Abi.RegIsa.loc
    where type Abi.RegIsa.Program.Builder.builder = Args.Abi.RegIsa.Program.Builder.builder
    where type Hints.t = Args.Hints.t
    where type Hints.Location.t = Args.Hints.Location.t
= struct
    structure Abi = Args.Abi
    structure Hints = Args.Hints
    structure Location = Hints.Location
    structure Register = Abi.RegIsa.Register
    structure Stmt = Abi.RegIsa.Stmt
    structure Builder = Abi.RegIsa.Program.Builder
    structure CallingConvention = Abi.CallingConvention

    datatype either = datatype Either.t
    datatype location = datatype Location.t
    type builder = Builder.builder
    type hints = Hints.t

    val op|> = Fn.|>

    val isCalleeSave = CallingConvention.isCalleeSave Abi.foreignCallingConvention

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

    structure Registers :> sig
        type t

        (* All registers unoccupied. *)
        val empty : t
        (* Try to allocate a register for the id.
           Return `NONE` if out of registers. *)
        val allocate : t -> hints -> CpsId.t -> (t * Register.t) option
        (* Try to allocate a register for the id satisfying the predicate.
           Return `NONE` if out of satisfactory registers. *)
        val allocateEnsuring : t -> (Register.t -> bool) -> CpsId.t -> (t * Register.t) option
        (* Try to allocate the specific register for the id.
           Return `Left otherId` if the register is occupied by otherId. *)
        val allocateFixed : t -> CpsId.t -> Register.t -> (CpsId.t, t) Either.t
        (* Free the register. *)
        val free : t -> Register.t -> t
        val lookup : t -> Register.t -> CpsId.t
    end = struct
        structure Map = Register.SortedMap

        type t = { occupieds : CpsId.t Map.map
                 , frees : Register.t list }

        fun extract pred =
            fn x :: xs =>
                if pred x
                then SOME (xs, x)
                else Option.map (fn (xs, y) => (x :: xs, y)) (extract pred xs)
             | [] => NONE

        val empty : t = { occupieds = Map.empty
                        , frees = VectorExt.toList Abi.generalRegs }

        fun allocateFixed (regs as {occupieds, frees}) id reg =
            case Map.find (occupieds, reg)
            of SOME currentId =>
                if currentId = id
                then Right regs
                else Left currentId
             | NONE =>
                let val frees = valOf (pickEq frees reg)
                in Right {occupieds = Map.insert (occupieds, reg, id), frees}
                end

        fun allocate regs hints id =
            let val rec loop =
                    fn Register hint :: hints =>
                        (case allocateFixed regs id hint
                         of Left _ => loop hints
                          | Right regs => SOME (regs, hint))
                     | StackSlot _ :: hints => loop hints
                     | [] => 
                        let val {occupieds, frees} = regs
                        in  case frees
                            of reg :: frees =>
                                SOME ({occupieds = Map.insert (occupieds, reg, id), frees}, reg)
                             | [] => NONE
                        end
            in loop (Hints.find hints id)
            end

        fun allocateEnsuring ({occupieds, frees}) pred id =
            Option.map (fn (frees, reg) =>
                            ({occupieds = Map.insert (occupieds, reg, id), frees}, reg))
                       (extract pred frees)

        fun free (regs as {occupieds, frees}) reg =
            if Map.inDomain (occupieds, reg)
            then { occupieds = #1 (Map.remove (occupieds, reg))
                 , frees = reg :: frees }
            else regs

        fun lookup ({occupieds, ...} : t) reg = Map.lookup (occupieds, reg)
    end

    structure StackFrame :> sig
        type t

        val empty : int ref -> t
        val lookup : t -> StackSlot.t -> CpsId.t
        val allocate : t -> CpsId.t -> t * StackSlot.t
        val free : t -> StackSlot.t -> t
    end = struct
        structure Map = StackSlot.SortedMap
        structure Pool = StackSlot.Pool

        type t = { occupieds : CpsId.t Map.map, frees : Pool.t}

        fun empty maxSlotCount = {occupieds = Map.empty, frees = Pool.empty maxSlotCount}

        fun lookup ({occupieds, ...} : t) slot = Map.lookup (occupieds, slot)

        fun allocate {occupieds, frees} id =
            let val (frees, slot) = Pool.allocate frees
            in ({occupieds = Map.insert (occupieds, slot, id), frees}, slot)
            end

        fun free (frame as {occupieds, frees}) slot =
            if Map.inDomain (occupieds, slot)
            then { occupieds = #1 (Map.remove (occupieds, slot))
                 , frees = Pool.free frees slot }
            else frame
    end

    datatype location = datatype Location.t

    type t = { locations : Location.SortedSet.set CpsId.SortedMap.map
             , registers : Registers.t
             , frame : StackFrame.t }

(* # Pure Env operations *)

    fun empty maxSlotCount =
        { locations = CpsId.SortedMap.empty
        , registers = Registers.empty
        , frame = StackFrame.empty maxSlotCount }

    fun locationsOf ({locations, ...} : t) id = CpsId.SortedMap.find (locations, id)

    fun insertLocation locations id loc =
        let val idLocs = getOpt (CpsId.SortedMap.find (locations, id), Location.SortedSet.empty)
        in CpsId.SortedMap.insert (locations, id, Location.SortedSet.add (idLocs, loc))
        end

    fun findReg env id =
        locationsOf env id
        |> Option.mapPartial (Location.SortedSet.find Location.isReg)
        |> Option.map (fn Register reg => reg
                        | StackSlot _ => raise Fail "unreachable")

    fun allocate ({locations, registers, frame}) hints id =
        case Registers.allocate registers hints id
        of SOME (registers, reg) =>
            let val loc = Register reg
            in ( { locations = insertLocation locations id loc
                 , registers, frame }
               , loc )
            end
         | NONE =>
            let val (frame, slot) = StackFrame.allocate frame id
                val loc = StackSlot slot
            in ( { locations = insertLocation locations id loc
                 , registers, frame }
               , loc )
            end

    fun freeLocation (env as {locations, registers, frame}) id loc =
        let val idLocs = Location.SortedSet.delete (valOf (locationsOf env id), loc)
            val locations =
                if Location.SortedSet.isEmpty idLocs
                then #1 (CpsId.SortedMap.remove (locations, id))
                else CpsId.SortedMap.insert (locations, id, idLocs)
        in  case loc
            of Register reg =>
                {locations, registers = Registers.free registers reg, frame}
             | StackSlot slot =>
                {locations, registers, frame = StackFrame.free frame slot}
        end

(* # Effectful Building Blocks *)

    fun evacuateTo env builder label src target =
        if not (Location.eq (src, target))
        then case (src, target)
             of (srcLoc as Register src, Register target) =>
                 let val {registers, ...} = env
                     val srcId = Registers.lookup registers src
                 in Builder.insertStmt builder label (Stmt.Def (src, Abi.RegIsa.Instrs.Oper.move target))
                  ; freeLocation env srcId srcLoc
                 end
              | (srcLoc as Register src, StackSlot target) =>
                 let val {registers, ...} = env
                     val srcId = Registers.lookup registers src
                     val oper = Abi.RegIsa.Instrs.Oper.stackLoad Abi.sp (StackSlot.index target)
                 in Builder.insertStmt builder label (Stmt.Def (src, oper))
                  ; freeLocation env srcId srcLoc
                 end
              | (srcLoc as StackSlot src, Register target) =>
                 let val {frame, ...} = env
                     val srcId = StackFrame.lookup frame src
                     val oper = Abi.RegIsa.Instrs.Oper.stackStore Abi.sp (StackSlot.index src) target
                 in Builder.insertStmt builder label (Stmt.Eff oper)
                  ; freeLocation env srcId srcLoc
                 end
              | (StackSlot src, StackSlot target) =>
                 raise Fail "unimplemented"
        else env

    fun evacuateReg env hints builder label id reg =
        let val (env, loc') = allocate env hints id
        in evacuateTo env builder label (Register reg) loc'
        end

    fun evacuateEnsuring env builder label pred id loc =
        raise Fail "unimplemented"

    fun freeIn env builder label id reg =
        case locationsOf env id
        of SOME idLocs =>
            let val (origLoc, origReg) =
                    case Location.SortedSet.find (fn Register reg' => Register.eq (reg', reg)
                                                   | StackSlot _ => false)
                                                 idLocs
                    of SOME (origLoc as Register origReg) => (origLoc, origReg)
                     | SOME (StackSlot _) => raise Fail "unreachable"
                     | NONE => raise Fail "unimplemented"
                val env =
                    Location.SortedSet.foldl (fn (loc as Register reg, env) =>
                                                  if Register.eq (reg, origReg)
                                                  then env
                                                  else evacuateTo env builder label loc origLoc
                                               | (loc as StackSlot _, env) =>
                                                  evacuateTo env builder label loc origLoc)
                                             env idLocs
            in freeLocation env id origLoc
            end
         | NONE => raise Fail "unreachable"

    fun free env builder label id =
        case locationsOf env id
        of SOME idLocs =>
            let val (origLoc, origReg) =
                    case Location.SortedSet.find Location.isReg idLocs
                    of SOME (origLoc as Register origReg) => (origLoc, origReg)
                     | SOME (StackSlot _) => raise Fail "unreachable"
                     | NONE => raise Fail "unimplemented"
                val env =
                    Location.SortedSet.foldl (fn (loc as Register reg, env) =>
                                                  if Register.eq (reg, origReg)
                                                  then env
                                                  else evacuateTo env builder label loc origLoc
                                               | (loc as StackSlot _, env) =>
                                                  evacuateTo env builder label loc origLoc)
                                             env idLocs
            in freeLocation env id origLoc
            end
         | NONE => raise Fail "unreachable"

(* # Public API *)

    fun regUse env hints builder label id =
        case findReg env id
        of SOME reg => (env, reg)
         | NONE =>
            let val {locations, registers, frame} = env
            in  case Registers.allocate registers hints id
                of SOME (registers, reg) =>
                    ( { locations = insertLocation locations id (Register reg)
                      , registers, frame }
                    , reg )
                 | NONE => raise Fail "unimplemented"
            end

    fun fixedRegUse (env as {locations, registers, frame} : t) hints builder label id reg =
        case Registers.allocateFixed registers id reg
        of Right registers =>
            { locations = insertLocation locations id (Register reg)
            , registers, frame }
         | Left occupant =>
            let val env = evacuateReg env hints builder label occupant reg
            in fixedRegUse env hints builder label id reg
            end

    fun fixedUse env hints builder label id =
        fn Register reg => fixedRegUse env hints builder label id reg

    fun regDef env hints builder label id =
        let val (env, reg) = regUse env hints builder label id
            val env = free env builder label id
        in (env, reg)
        end

    fun fixedRegDef env hints builder label id reg =
        let val env = fixedRegUse env hints builder label id reg
        in freeIn env builder label id reg
        end

    fun fixedDef env hints builder label id =
        fn Register reg => fixedRegDef env hints builder label id reg

    fun evacuateCallerSaves (env as {locations, ...} : t) builder label =
        let fun step (id, idLocs, env) =
                let val (env, idLocs, loc') =
                        case Location.SortedSet.find isCalleeSave idLocs
                        of SOME loc' => (env, idLocs, loc')
                         | NONE =>
                            let val {registers, locations, frame} = env
                                val (env, loc') =
                                    case Registers.allocateEnsuring registers (isCalleeSave o Register) id
                                    of SOME (registers, reg) =>
                                        let val loc' = Register reg
                                        in ( { locations = insertLocation locations id loc'
                                             , registers, frame }
                                           , loc' )
                                        end
                                     | NONE =>
                                        let val (frame, slot) = StackFrame.allocate frame id
                                            val loc' = StackSlot slot
                                        in ( { locations = insertLocation locations id loc'
                                             , registers, frame }
                                           , loc' )
                                        end
                            in (env, valOf (locationsOf env id), loc')
                            end
                    fun step (loc, env) =
                        if isCalleeSave loc orelse Location.eq (loc, loc')
                        then env
                        else evacuateTo env builder label loc loc'
                in Location.SortedSet.foldl step env idLocs
                end
        in CpsId.SortedMap.foldli step env locations
        end

    fun conform (env as {locations, ...} : t) hints builder label ({locations = locations', ...} : t) =
        let fun step (id, _, env) =
                let val locs' = CpsId.SortedMap.lookup (locations', id)
                    val loc' = if Location.SortedSet.numItems locs' <> 1
                               then raise Fail "unimplemented"
                               else Location.SortedSet.minItem locs'
                in  case loc'
                    of Register reg => fixedRegDef env hints builder label id reg
                     | StackSlot slot => raise Fail "unimplemented"
                end
        in ignore (CpsId.SortedMap.foldli step env locations)
        end

    fun incCounts counts ({locations, ...} : t) =
        let fun idLocsToCounts idLocs =
                let fun step (loc, idCounts) =
                        let val count = getOpt (Location.SortedMap.find (idCounts, loc), 0)
                        in Location.SortedMap.insert (idCounts, loc, count + 1)
                        end
                in Location.SortedSet.foldl step Location.SortedMap.empty idLocs
                end
        in CpsId.SortedMap.unionWith (Location.SortedMap.unionWith op+)
                                     (counts, CpsId.SortedMap.map idLocsToCounts locations)
        end

    fun fromCounts maxSlotCount counts =
        let val hints = Hints.fromCounts counts
        in CpsId.SortedMap.foldli (fn (id, _, env) => #1 (allocate env hints id))
               (empty maxSlotCount) counts
        end
end

