functor IsaLabelUsesFn (Isa : ISA) :> sig
    val useCounts : Isa.Program.t -> {exports : int, escapes : int, calls : int} Cps.Program.LabelMap.t
end = struct
    structure LabelMap = Cps.Program.LabelMap

    datatype stmt = datatype Isa.Stmt.t

    fun useCounts {conts, main} =
        let val counts = ref LabelMap.empty

            fun export label =
                counts := LabelMap.update (!counts) label (fn
                    | SOME {exports, escapes, calls} => {exports = exports + 1, escapes, calls}
                    | NONE => {exports = 1, escapes = 0, calls = 0}
                )

            fun escape label =
                counts := LabelMap.update (!counts) label (fn
                    | SOME {exports, escapes, calls} => {exports, escapes = escapes + 1, calls}
                    | NONE => {exports = 0, escapes = 1, calls = 0}
                )

            fun call label =
                counts := LabelMap.update (!counts) label (fn
                    | SOME {exports, escapes, calls} => {exports, escapes, calls = calls + 1}
                    | NONE => {exports = 0, escapes = 0, calls = 1}
                )

            val usesInExpr = Isa.Instrs.Oper.appLabels escape

            val usesInStmt =
                fn Def (_, expr) => usesInExpr expr
                 | Eff expr => usesInExpr expr
                 | Param _ => ()

            val usesInTransfer = Isa.Instrs.Transfer.appLabels call

            fun usesInCont (_, {name = _, argc = _, stmts, transfer}) =
                ( Vector.app usesInStmt stmts
                ; usesInTransfer transfer )

            do export main
            do LabelMap.appi usesInCont conts
        in !counts
        end
end

