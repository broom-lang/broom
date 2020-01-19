signature LABEL_USES = sig
    structure Isa : ISA

    type t = {exports : int, escapes : int, calls : int} Label.HashMap.t

    val useCounts : Isa.Program.t -> t
end

functor IsaLabelUsesFn (Isa : ISA) :> LABEL_USES
    where type Isa.loc = Isa.loc
    where type Isa.Stmt.t = Isa.Stmt.t
    where type Isa.transfer = Isa.transfer
= struct
    structure Isa = Isa
    structure LabelMap = Label.HashMap

    datatype stmt = datatype Isa.Stmt.t

    type t = {exports : int, escapes : int, calls : int} Label.HashMap.t

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

            val usesInTransfer = Isa.Instrs.Transfer.appLabels call

            fun usesInCont (_, {name = _, cconv = _, params = _, stmts, transfer}) =
                ( Vector.app usesInStmt stmts
                ; usesInTransfer transfer )

            do export main
            do LabelMap.appi usesInCont conts
        in !counts
        end
end

