functor ScheduleParamsFn (Isa : ISA) :> sig
    val schedule : Isa.Program.t -> Isa.Program.t
end = struct
    structure Stmt = Isa.Stmt
    structure Transfer = Isa.Transfer
    structure LabelMap = Cps.Program.LabelMap (* HACK *)

    val compareStmts =
        (* NOTE: `Param` labels are always equal: *)
        fn (Stmt.Param (_, _, i), Stmt.Param (_, _, i')) => Int.compare (i, i')
         | (Stmt.Param _, _) => LESS
         | (_, Stmt.Param _) => GREATER
         | _ => EQUAL (* leverage sort stability *)

    val scheduleStmts = Vector.stableSort compareStmts

(* HACK: Inserting prologue here is not very semantic but most convenient: *)
    fun scheduleCont {name, cconv, argc, stmts, transfer} =
        let val stmts = scheduleStmts stmts
            val stmts =
                if Option.isSome cconv
                then Vector.prepend (Stmt.Prologue, stmts)
                else stmts
            val stmts =
                if Transfer.isReturn transfer
                then Vector.append (stmts, Stmt.Epilogue)
                else stmts
        in {name, cconv, argc, stmts, transfer}
        end

    fun schedule {conts, main} =
        {conts = LabelMap.map scheduleCont conts, main}
end

structure X64ScheduleParams = ScheduleParamsFn(X64Isa)

