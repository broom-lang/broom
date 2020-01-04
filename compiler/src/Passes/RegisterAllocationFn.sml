functor RegisterAllocationFn (Registerizer : REGISTERIZER) :> sig
    val allocate : Registerizer.Abi.Isa.Program.t -> Registerizer.Abi.RegIsa.Program.t
end = struct
    structure LabelMap = Cps.Program.LabelMap
    structure Abi = Registerizer.Abi
    structure Isa = Abi.Isa
    structure Register = Isa.Register
    structure Transfer = Isa.Transfer
    structure Builder = Abi.RegIsa.Program.Builder
    structure LabelUses = IsaLabelUsesFn(Isa)
    structure LastUses = LastUsesFn(struct
        structure Isa = Isa
        structure LabelUses = LabelUses
    end)
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
            val lastUses = LastUses.analyze program useCounts
            
            val cconvs = Label.HashTable.mkTable (0, Subscript)
            do LabelMap.appi (fn kv as (label, _) =>
                                  case aPrioriCallingConvention useCounts kv
                                  of SOME cconv =>
                                      Label.HashTable.insert cconvs (label, cconv)
                                   | NONE => ())
                             conts
            val builder = Builder.new ()
            
            fun allocateStmt label (stmt, env) =
                Registerizer.stmt cconvs builder label env stmt

            fun allocateSucc (label, env) =
                allocateEBB label env (LabelMap.lookup conts label)

            and allocateTransfer label transfer =
                let val env =
                        getOpt ( Transfer.foldLabels (SOME o allocateSucc) NONE transfer
                               , Env.empty )
                in Registerizer.transfer cconvs builder label env transfer
                end

            and allocateEBB label entryEnv {name, argc, stmts, transfer} =
                let do Builder.createCont builder label {name, argc}
                    val env = allocateTransfer label transfer
                    (* TODO: Shuffling to match `entryEnv` or calling convention *)
                    do Label.HashTable.insert cconvs (label, #[]) (* FIXME *)
                in Vector.foldr (allocateStmt label) env stmts
                end

            fun allocateCont (label, cont) =
                let val {exports, escapes, calls} = LabelMap.lookup useCounts label
                in  if exports > 0 orelse escapes > 0 orelse calls > 1
                    then ignore (allocateEBB label NONE cont)
                    else ()
                end

            do LabelMap.appi allocateCont conts
            val {conts, main} = Builder.build builder main
            
            (* HACK: Stmts were pushed to builder in reverse, so need to..: *)
            fun reverseStmts {name, argc, stmts, transfer} =
                {name, argc, stmts = Vector.rev stmts, transfer}
        in {conts = LabelMap.map reverseStmts conts, main}
        end
end

