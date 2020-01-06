structure X64SysVAbi :> ABI
    where type Isa.Instrs.Oper.t = X64Isa.Instrs.Oper.t
    where type Isa.Stmt.t = X64Isa.Stmt.t
    where type Isa.Transfer.t = X64Isa.Transfer.t
    where type RegIsa.Register.t = X64RegIsa.Register.t
    where type RegIsa.Instrs.Oper.t = X64RegIsa.Instrs.Oper.t
    where type RegIsa.Stmt.t = X64RegIsa.Stmt.t
    where type RegIsa.Transfer.t = X64RegIsa.Transfer.t
= struct
    structure LabelMap = Cps.Program.LabelMap
    structure Isa = X64Isa
    structure Reg = X64Register
    structure RegIsa = X64RegIsa
    structure Stmt = X64RegIsa.Stmt
    structure Builder = RegIsa.Program.Builder
    structure CallingConvention = CallingConventionFn(Reg)
    structure LabelUses = IsaLabelUsesFn(Isa)

    datatype oper = datatype X64RegInstructions.Oper.t
    datatype transfer = datatype X64RegInstructions.Transfer.t

    val generalRegs =
        #[ Reg.rax, Reg.rdx, Reg.rcx, Reg.rbx, Reg.rsi, Reg.rdi
         , Reg.r8, Reg.r9, Reg.r10, Reg.r11, Reg.r12, Reg.r13, Reg.r14, Reg.r15 ]

    (* NOTE: Technically rsp is caller-save and rbp callee-save but they
             are handled specially: *)
    val foreignCallingConvention =
        { args = #[Reg.rdi, Reg.rsi, Reg.rdx, Reg.rcx, Reg.r8, Reg.r9]
        , retVal = #[Reg.rax]
        , callerSaves = #[ Reg.rax, Reg.rcx, Reg.rdx, Reg.rdi, Reg.rsi
                         , Reg.r8, Reg.r9, Reg.r10, Reg.r11 ]
        , calleeSaves = #[Reg.rbx, Reg.r12, Reg.r13, Reg.r14, Reg.r15] }

    val exporteeCallingConvention =
        Vector.concat [ #args foreignCallingConvention
                      , #[Reg.rbx, Reg.r12, Reg.r13, Reg.r14, Reg.r15] ]

    val escapeeCallingConvention = #args foreignCallingConvention

    val sp = Reg.rsp
end

