structure X64InstrSelection = InstrSelectionFn(struct
    structure Isa = X64Isa

    datatype instr = datatype Isa.Instrs.Oper.t
    datatype stmt = datatype Isa.Stmt.t
    datatype transfer = datatype X64Instructions.Transfer.t

    structure Implement = struct
        fun expr contBuilder def =
            fn Cps.Expr.Param (label, i) =>
                Isa.Cont.Builder.insertStmt contBuilder (Param (def, label, i))
             | _ => () (* FIXME *)

        fun transfer builder contBuilder =
            fn Cps.Cont.Transfer.Goto {callee, tArgs = _, vArgs} => JMP (callee, vArgs)
             | Cps.Cont.Transfer.Jump {callee, tArgs = _, vArgs} => JMPi (callee, vArgs)
             | Cps.Cont.Transfer.Match (matchee, #[{pattern = Any, target}]) =>
                JMP (target, #[])
    end
end)

