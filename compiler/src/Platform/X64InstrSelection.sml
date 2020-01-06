structure X64InstrSelection = InstrSelectionFn(struct
    structure Isa = X64Isa
    structure Builder = Isa.Program.Builder

    datatype oper = datatype Cps.Expr.oper
    datatype transfer = datatype Cps.Cont.Transfer.t
    datatype instr = datatype X64Instructions.Oper.t
    datatype stmt = datatype Isa.Stmt.t
    datatype transfer = datatype X64Instructions.Transfer.t

    structure Implement = struct
        fun expr builder parent def =
            fn ClosureNew (label, #[]) =>
                let val size = CpsId.fresh ()
                    val ldef = CpsId.fresh ()
                in expr builder parent size (Const (Const.Int 8))
                 ; Builder.insertStmt builder parent (Def (def, CALLd ("malloc", #[size])))
                 ; Builder.insertStmt builder parent (Def (ldef, LOADl label))
                 ; Builder.insertStmt builder parent (Eff (STORE (def, ldef)))
                end
             | ClosureFn closure =>
                Builder.insertStmt builder parent (Def (def, LOAD closure))
             | EmptyRecord =>
                Builder.insertStmt builder parent (Def (def, LOADc 0w0))
             | Cps.Expr.Param (label, i) =>
                Builder.insertStmt builder parent (Param (def, label, i))
             | PrimApp {opn, tArgs = _, vArgs} =>
                (case opn
                 of StackNew => (* HACK: *)
                     Builder.insertStmt builder parent (Def (def, LOADc 0w0)))
             | Const (Const.Int n) => (* FIXME: `n` might not fit into 32 bits: *)
                Builder.insertStmt builder parent (Def (def, LOADc (Word32.fromInt n)))
             | _ => () (* FIXME *)

        fun transfer builder =
            fn Goto {callee, tArgs = _, vArgs} => JMP (callee, vArgs)
             | Jump {callee, tArgs = _, vArgs} => JMPi (callee, vArgs)
             | Match (matchee, #[{pattern = Any, target}]) => JMP (target, #[])
             | Return (_, args) => RET args
    end
end)

