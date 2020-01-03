functor RegisterAllocationFn (Args : sig
    structure Abi : ABI
end) :> sig
    val allocate : Args.Abi.Isa.Program.t -> Args.Abi.RegIsa.Program.t
end = struct
    structure LabelMap = Cps.Program.LabelMap
    structure Abi = Args.Abi
    structure Isa = Abi.Isa
    structure Register = Isa.Register
    structure Transfer = Isa.Transfer
    structure Env = Abi.Env
    structure Builder = Abi.RegIsa.Program.Builder
    structure LabelUses = IsaLabelUsesFn(Isa)
    structure LastUses = LastUsesFn(struct
        structure Isa = Isa
        structure LabelUses = LabelUses
    end)

    fun aPrioriCallingConvention useCounts (label, cont) =
        let val {exports, escapes, calls} = LabelMap.lookup useCounts label
        in  if exports > 0
            then SOME Abi.exporteeCallingConvention
            else if escapes > 0
                 then SOME Abi.escapeeCallingConvention
                 else NONE
        end

    fun allocate (program as {conts, main}) =
        let val useCounts = LabelUses.useCounts program
            val lastUses = LastUses.analyze program useCounts
            
            val callingConventions = Label.HashTable.mkTable (0, Subscript)
            do LabelMap.appi (fn kv as (label, _) =>
                                  case aPrioriCallingConvention useCounts kv
                                  of SOME cconv =>
                                      Label.HashTable.insert callingConventions (label, cconv)
                                   | NONE => ())
                             conts
            val builder = Builder.new ()

            fun allocateStmt label (i, stmt, env) =
                Abi.stmt lastUses callingConventions builder label env i stmt

            fun allocateTransfer label env transfer =
                let val env = Abi.transfer lastUses callingConventions builder label env transfer
                in Transfer.appLabels (fn label =>
                                           let val cont = LabelMap.lookup conts label
                                           in allocateEBB label env cont
                                           end)
                                      transfer
                end

            and allocateEBB label env {name, argc, stmts, transfer} =
                let do Builder.createCont builder label {name, argc}
                    val env = Vector.foldli (allocateStmt label) env stmts
                in allocateTransfer label env transfer
                end

            fun allocateCont (label, cont) =
                let val {exports, escapes, calls} = LabelMap.lookup useCounts label
                in  if exports > 0 orelse escapes > 0 orelse calls > 1
                    then allocateEBB label Env.empty cont
                    else ()
                end

            do LabelMap.appi allocateCont conts
        in Builder.build builder main
        end
end

