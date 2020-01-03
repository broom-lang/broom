signature ABI = sig
    structure Isa : ISA where type def = CpsId.t
    structure Reg : REGISTER
    structure RegIsa : ISA where type def = Reg.t
    structure CallingConvention : CALLING_CONVENTION
        where type Register.t = RegIsa.Register.t
    structure LastUses : LAST_USES
    structure Env : REGISTER_ENV

    val exporteeCallingConvention : CallingConvention.internal
    val escapeeCallingConvention : CallingConvention.internal

    val stmt : LastUses.program_luses -> CallingConvention.internal Label.HashTable.hash_table
        -> RegIsa.Program.Builder.builder -> Label.t -> Env.t -> int -> Isa.Stmt.t -> Env.t
    val transfer : LastUses.program_luses  -> CallingConvention.internal Label.HashTable.hash_table
        -> RegIsa.Program.Builder.builder -> Label.t -> Env.t -> Isa.Transfer.t -> Env.t
end

