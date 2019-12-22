structure ContEscapism :> sig
    val specialize : Cps.Program.t -> Cps.Program.t
end = struct
    fun specialize program = program
end

