signature ABI = sig
    structure Isa : ISA where type def = CpsId.t
    structure Reg : REGISTER
    structure RegIsa : ISA where type def = Reg.t
    structure CallingConvention : CALLING_CONVENTION
        where type Register.t = RegIsa.Register.t
    structure LastUses : LAST_USES

    val generalRegs : RegIsa.Register.t vector
    val exporteeCallingConvention : CallingConvention.internal
    val escapeeCallingConvention : CallingConvention.internal
end

