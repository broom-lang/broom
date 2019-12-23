structure ClosureConvert :> sig
    val convert : Cps.Program.t -> Cps.Program.t
end = struct
    fun convert program = program
end

