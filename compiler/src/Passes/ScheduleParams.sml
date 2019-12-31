functor ScheduleParamsFn (Isa : ISA) :> sig
    val schedule : Isa.Program.t -> Isa.Program.t
end = struct
    structure Stmt = Isa.Stmt
    structure LabelMap = Cps.Program.LabelMap (* HACK *)

    val compareStmts =
        (* NOTE: `Param` labels are always equal at this point: *)
        fn (Stmt.Param (_, _, i), Stmt.Param (_, _, i')) => Int.compare (i, i')
         | (Stmt.Param _, _) => LESS
         | (_, Stmt.Param _) => GREATER
         | (_, _) => LESS

    (* FIXME: Need a stable sort: *)
    fun scheduleStmts stmts = Vector.sort compareStmts stmts

    fun scheduleCont {name, argc, stmts, transfer} =
        {name, argc, stmts = scheduleStmts stmts, transfer}

    fun schedule {conts, main} =
        {conts = LabelMap.map scheduleCont conts, main}
end

structure X64ScheduleParams = ScheduleParamsFn(X64Isa)

