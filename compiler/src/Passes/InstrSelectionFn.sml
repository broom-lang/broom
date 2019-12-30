functor InstrSelectionFn (Args : sig
    structure Isa : ISA

    structure Implement : sig
        val expr : Isa.Cont.Builder.builder -> CpsId.t -> Cps.Expr.oper -> unit
        val transfer : Isa.Program.Builder.builder -> Isa.Cont.Builder.builder
            -> Cps.Cont.Transfer.t -> Isa.Transfer.t
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
            val visitedLabels = Label.HashSetMut.mkEmpty 0

            fun selectExpr contBuilder visitedDefs def =
                fn {parent = SOME parent, oper} =>
                    ( Cps.Expr.foldLabels (fn (label, ()) => selectLabel label)
                                          () oper
                    ; Cps.Expr.foldDeps (fn (def, ()) =>
                                             selectDef contBuilder visitedDefs def)
                                        () oper
                    ; Implement.expr contBuilder def oper )
                 | {parent = NONE, oper = _} => raise Fail "unreachable"

            and selectDef contBuilder visitedDefs def =
                if not (CpsId.HashSetMut.member (visitedDefs, def))
                then ( CpsId.HashSetMut.add (visitedDefs, def)
                     ; selectExpr contBuilder visitedDefs def (Cps.Program.defSite program def) )
                else ()

            and selectTransfer contBuilder visitedDefs transfer =
                ( Cps.Cont.Transfer.foldLabels (fn (label, ()) => selectLabel label)
                                               () transfer
                ; Cps.Cont.Transfer.foldDeps (fn (def, ()) =>
                                                  selectDef contBuilder visitedDefs def)
                                             () transfer
                ; Implement.transfer builder contBuilder transfer )

            and selectCont (label, {name, tParams = _, vParams, body}) =
                let val contBuilder = Cont.Builder.new {name, argc = Vector.length vParams}
                    val visitedDefs = CpsId.HashSetMut.mkEmpty 0
                    val body = selectTransfer contBuilder visitedDefs body
                in Builder.insertCont builder label (Cont.Builder.build contBuilder body)
                end

            and selectLabel label =
                if not (Label.HashSetMut.member (visitedLabels, label))
                then ( Label.HashSetMut.add (visitedLabels, label)
                     ; selectCont (label, Cps.Program.labelCont program label) )
                else ()

            do selectLabel main
        in Builder.build builder main
        end
end

