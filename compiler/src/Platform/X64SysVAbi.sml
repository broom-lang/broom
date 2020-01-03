structure X64SysVAbi :> ABI
    where type Isa.Stmt.t = X64Isa.Stmt.t
    where type Isa.Transfer.t = X64Isa.Transfer.t
    where type RegIsa.Stmt.t = X64RegIsa.Stmt.t
    where type RegIsa.Transfer.t = X64RegIsa.Transfer.t
= struct
    structure Isa = X64Isa
    structure Reg = X64Register
    structure RegIsa = X64RegIsa
    structure CallingConvention = CallingConventionFn(Reg)
    structure LabelUses = IsaLabelUsesFn(Isa)
    structure LastUses = LastUsesFn(struct
        structure Isa = Isa
        structure LabelUses = LabelUses
    end)
    structure Env = RegisterEnvFn(Reg)

    val foreignCallingConvention =
        { args = #[Reg.rdi, Reg.rsi, Reg.rdx, Reg.rcx, Reg.r8, Reg.r9]
        , retVal = #[Reg.rax]
        , callerSaves = #[ Reg.rax, Reg.rcx, Reg.rdx, Reg.rdi, Reg.rsi, Reg.rsp
                         , Reg.r8, Reg.r9, Reg.r10, Reg.r11 ]
        , calleeSaves = #[ Reg.rbx, Reg.rbp
                         , Reg.r12, Reg.r13, Reg.r14, Reg.r15 ] }

    val exporteeCallingConvention =
        Vector.concat [ #args foreignCallingConvention
                      , #[Reg.rbx, Reg.r12, Reg.r13, Reg.r14, Reg.r15] ]

    val escapeeCallingConvention = #args foreignCallingConvention

    fun stmt _ _ _ = raise Fail "unimplemented"

    fun transfer _ _ _ = raise Fail "unimplemented"
end

