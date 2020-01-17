structure X64InsertLogues = InsertLoguesFn(struct
    structure RegIsa = X64RegIsa
    structure Reg = X64Register
    structure Oper = X64RegInstructions.Oper
    structure Stmt = RegIsa.Stmt

    fun prologue frameSize =
        #[ Stmt.Eff (Oper.PUSH Reg.rbp)
         , Stmt.Def (Reg.rbp, Oper.MOV Reg.rsp)
         , Stmt.Def (Reg.rsp, Oper.SUBc (Reg.rsp, frameSize)) ]

    fun epilogue frameSize = #[Stmt.Eff Oper.LEAVE]
end)

