signature LOGUES = sig
    structure RegIsa : ISA

    val insert : {program : RegIsa.Program.t, maxSlotCount : int} -> RegIsa.Program.t
end

