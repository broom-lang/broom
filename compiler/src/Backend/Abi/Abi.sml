signature ABI = sig
    structure Isa : ISA where type def = CpsId.t
    structure RegIsa : ISA
    structure CallingConvention : CALLING_CONVENTION
        where type Location.t = RegIsa.loc
        where type Location.Register.t = RegIsa.def

    val generalRegs : RegIsa.Register.t vector
    val exporteeCallingConvention : CallingConvention.internal
    val escapeeCallingConvention : CallingConvention.internal
    val foreignCallingConvention : CallingConvention.foreign
    val sp : RegIsa.Register.t
end

