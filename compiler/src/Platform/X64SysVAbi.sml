structure X64SysVAbi :> ABI
    where type Isa.oper = X64Isa.oper
    where type Isa.Stmt.t = X64Isa.Stmt.t
    where type Isa.transfer = X64Isa.transfer
    where type RegIsa.def = X64RegIsa.def
    where type RegIsa.loc = X64Location.t
    where type RegIsa.oper = X64RegIsa.oper
    where type RegIsa.Stmt.t = X64RegIsa.Stmt.t
    where type RegIsa.transfer = X64RegIsa.transfer
= struct
    structure LabelMap = Label.SortedMap
    structure Isa = X64Isa
    structure Reg = X64Register
    structure RegIsa = X64RegIsa
    structure Stmt = X64RegIsa.Stmt
    structure Builder = RegIsa.Program.Builder
    structure Location = X64Location
    structure CallingConvention = CallingConventionFn(Location)
    structure LabelUses = IsaLabelUsesFn(Isa)

    datatype oper = datatype X64RegInstructions.Oper.t

    val op|> = Fn.|>

    val generalRegs =
        #[ Reg.rax, Reg.rdx, Reg.rcx, Reg.rbx, Reg.rsi, Reg.rdi
         , Reg.r8, Reg.r9, Reg.r10, Reg.r11, Reg.r12, Reg.r13, Reg.r14, Reg.r15 ]

    (* NOTE: Technically rsp is caller-save and rbp callee-save but they
             are handled specially: *)
    val foreignCallingConvention =
        { args = #[Reg.rdi, Reg.rsi, Reg.rdx, Reg.rcx, Reg.r8, Reg.r9]
        , retVal = #[Reg.rax]
          (* NOTE: Technically rax is caller-save but should not be included here
                   since it is the return value: *)
        , callerSaves = #[ Reg.rcx, Reg.rdx, Reg.rdi, Reg.rsi
                         , Reg.r8, Reg.r9, Reg.r10, Reg.r11 ]
        , calleeSaves = #[Reg.rbx, Reg.r12, Reg.r13, Reg.r14, Reg.r15] }

    val exporteeCallingConvention =
        Vector.concat [ #args foreignCallingConvention
                      , #calleeSaves foreignCallingConvention ]
        |> Vector.map Location.Register

    val escapeeCallingConvention = #args foreignCallingConvention |> Vector.map Location.Register

    val sp = Reg.rsp
end

