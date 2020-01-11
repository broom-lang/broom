functor RegisterAllocationFn (Registerizer : REGISTERIZER) :> sig
    val allocate : Registerizer.Abi.Isa.Program.t
        -> {program : Registerizer.Abi.RegIsa.Program.t, maxSlotCount : int}
end = struct
    structure LabelMap = Cps.Program.LabelMap
    structure Abi = Registerizer.Abi
    structure Isa = Abi.Isa
    structure Register = Isa.Register
    structure Transfer = Isa.Transfer
    structure Builder = Abi.RegIsa.Program.Builder
    structure LabelUses = IsaLabelUsesFn(Isa)
    structure Env = Registerizer.Env

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
            val maxSlotCount = ref 0
            
            val cconvs = Label.HashTable.mkTable (0, Subscript)
            do LabelMap.appi (fn kv as (label, _) =>
                                  case aPrioriCallingConvention useCounts kv
                                  of SOME cconv =>
                                      Label.HashTable.insert cconvs (label, cconv)
                                   | NONE => ())
                             conts
            val builder = Builder.new ()

            fun allocateStmt label env hints stmt =
                Registerizer.stmt cconvs builder label env hints stmt

            fun allocateSucc hints (label, env) =
                let val {calls, ...} = LabelMap.lookup useCounts label
                in  if calls = 1
                    then allocateEBB label hints (LabelMap.lookup conts label)
                    else env
                end

            (* TODO: Multiple successors calling convention negotiation: *)
            and allocateTransfer label hints transfer =
                let val hints' = Registerizer.transferHints hints transfer
                    val env = Transfer.foldLabels (allocateSucc hints') (Env.empty maxSlotCount) transfer
                in Registerizer.transfer cconvs builder label env hints transfer
                end

            and allocateEBB label hints {name, cconv, argc, stmts, transfer} =
                let do Builder.createCont builder label {name, cconv, argc}
                    fun allocateBlock hints stmts =
                        case VectorSlice.uncons stmts
                        of SOME (stmt, stmts) =>
                            let val hints' = Registerizer.stmtHints hints stmt
                                val env = allocateBlock hints' stmts
                            in allocateStmt label env hints stmt
                            end
                         | NONE =>
                            let val env = allocateTransfer label hints transfer
                                (* TODO: Shuffling to match `entryEnv` or calling convention *)
                                do Label.HashTable.insert cconvs (label, #[]) (* FIXME *)
                            in env
                            end
                in allocateBlock hints (VectorSlice.full stmts)
                end

            fun allocateCont (label, cont) =
                let val {exports, escapes, calls} = LabelMap.lookup useCounts label
                in  if exports > 0 orelse escapes > 0 orelse calls > 1
                    then ignore (allocateEBB label Env.Hints.empty cont)
                    else ()
                end

            do LabelMap.appi allocateCont conts
            val {conts, main} = Builder.build builder main
            
            (* HACK: Stmts were pushed to builder in reverse, so need to..: *)
            fun reverseStmts {name, argc, cconv, stmts, transfer} =
                {name, argc, cconv, stmts = VectorExt.rev stmts, transfer}
        in { program = {conts = LabelMap.map reverseStmts conts, main}
           , maxSlotCount = !maxSlotCount }
        end
end

