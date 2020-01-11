(* TODO: Move portable parts out of here to a functor. *)
structure X64Logues :> LOGUES
    where type RegIsa.Stmt.t = X64RegIsa.Stmt.t
    where type RegIsa.transfer = X64RegIsa.transfer
= struct
    structure RegIsa = X64RegIsa
    structure Reg = X64Register
    structure Stmt = RegIsa.Stmt
    structure Transfer = RegIsa.Transfer
    structure Instrs = X64RegInstructions
    structure Oper = Instrs.Oper

    fun insert {program = {conts, main}, maxSlotCount} =
        let val frameSize = Word32.fromInt (maxSlotCount * Instrs.registerSize)

            val prologue =
                #[ Stmt.Eff (Oper.PUSH Reg.rbp)
                 , Stmt.Def (Reg.rbp, Oper.MOV Reg.rsp)
                 , Stmt.Def (Reg.rsp, Oper.SUBc (Reg.rsp, frameSize)) ]

            val epilogue = #[Stmt.Eff Oper.LEAVE]

            fun insertContLogues {name, cconv, argc, stmts, transfer} =
                let val stmts =
                        if Option.isSome cconv
                        then Vector.concat [prologue, stmts]
                        else stmts
                    val stmts =
                        if Transfer.isReturn transfer
                        then Vector.concat [stmts, epilogue]
                        else stmts
                in {name, cconv, argc, stmts, transfer}
                end
        in {conts = Cps.Program.LabelMap.map insertContLogues conts, main}
        end
end

