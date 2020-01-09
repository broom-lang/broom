functor InstrSelectionFn (Args : sig
    structure Isa : ISA

    structure Implement : sig
        val expr : Isa.Program.Builder.builder -> Label.t -> CpsId.t -> Cps.Expr.oper -> unit
        val transfer : Isa.Program.Builder.builder -> Cps.Cont.Transfer.t -> Isa.Transfer.t
    end
end) :> sig
    val selectInstructions : Cps.Program.t -> Args.Isa.Program.t
end = struct
    structure Cont = Args.Isa.Cont
    structure Builder = Args.Isa.Program.Builder
    structure Implement = Args.Implement

    datatype cps_transfer = datatype Cps.Cont.Transfer.t

    fun selectInstructions (program as {typeFns = _, stmts = _, conts, main}) =
        let val builder = Builder.new ()
            val visitedDefs = CpsId.HashSetMut.mkEmpty 0
            val visitedLabels = Label.HashSetMut.mkEmpty 0

            fun selectExpr def =
                fn {parent = SOME parent, oper} =>
                    ( Cps.Expr.foldLabels (fn (label, ()) => selectLabel label)
                                          () oper
                    ; Cps.Expr.foldDeps (fn (def, ()) => selectDef def)
                                        () oper
                    ; Implement.expr builder parent def oper )
                 | {parent = NONE, oper = _} => raise Fail "unreachable"

            and selectDef def =
                if not (CpsId.HashSetMut.member (visitedDefs, def))
                then ( CpsId.HashSetMut.add (visitedDefs, def)
                     ; selectExpr def (Cps.Program.defSite program def) )
                else ()

            and selectTransfer transfer =
                ( Cps.Cont.Transfer.foldLabels (fn (label, ()) => selectLabel label)
                                               () transfer
                ; Cps.Cont.Transfer.foldDeps (fn (def, ()) => selectDef def)
                                             () transfer
                ; Implement.transfer builder transfer )

            and selectCont (label, {name, cconv, tParams = _, vParams, body}) =
                ( Builder.createCont builder label {name, cconv, argc = Vector.length vParams}
                ; Builder.setTransfer builder label (selectTransfer body) )

            and selectLabel label =
                if not (Label.HashSetMut.member (visitedLabels, label))
                then ( Label.HashSetMut.add (visitedLabels, label)
                     ; selectCont (label, Cps.Program.labelCont program label) )
                else ()

            do selectLabel main
        in Builder.build builder main
        end
end

