structure X64InsertLogues = InsertLoguesFn(struct
    structure RegIsa = X64RegIsa
    structure Reg = X64Register
    structure Oper = X64RegInstructions.Oper
    structure Stmt = RegIsa.Stmt

    fun prologue pos frameSize =
        let val frameSize = (* Align stack pointer to 16 as per Sys V ABI: *)
                if LargeWord.mod (frameSize, 0w16) = 0w0
                then frameSize
                else frameSize + 0w8
        in  #[ Stmt.Eff (pos, Oper.PUSH Reg.rbp)
             , Stmt.Def (pos, Reg.rbp, RegIsa.Type.Prim PrimType.Int, Oper.MOV Reg.rsp)
             , Stmt.Def (pos, Reg.rsp, RegIsa.Type.Prim PrimType.Int, Oper.SUBc (Reg.rsp, frameSize)) ]
        end

    fun epilogue pos frameSize = #[Stmt.Eff (pos, Oper.LEAVE)]
end)

