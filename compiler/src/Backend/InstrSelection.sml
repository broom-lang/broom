functor InstrSelectionFn (Args : sig
    structure Isa : ISA

    structure Implement : sig
        val expr : Cps.Program.t -> Isa.Program.Builder.builder
            -> Label.t -> CpsId.t -> Cps.Type.t -> Cps.Expr.t -> CpsId.t vector
        val transfer : Isa.Program.Builder.builder -> Label.t -> Cps.Transfer.t -> Isa.Transfer.t
    end
end) :> sig
    val selectInstructions : Cps.Program.t -> Args.Isa.Program.t
end = struct
    structure Builder = Args.Isa.Program.Builder
    structure Implement = Args.Implement

    fun selectInstructions (program as {typeFns = _, globals = _, stmts = _, conts = _, main}) =
        let val builder = Builder.new ()
            val visitedDefs = CpsId.HashTable.mkTable (0, Subscript)
            val visitedLabels = Label.HashSetMut.mkEmpty 0

            fun selectExpr def =
                fn {pos = _, parent = SOME _, typ, oper = Cps.Expr.Result (tuple, i)} =>
                    let val vals =
                            if not (CpsId.HashTable.inDomain visitedDefs tuple)
                            then let val definiends = selectExpr tuple (Cps.Program.defSite program tuple)
                                 in CpsId.HashTable.insert visitedDefs (tuple, definiends)
                                  ; definiends
                                 end
                            else CpsId.HashTable.lookup visitedDefs tuple
                    in #[Vector.sub (vals, i)]
                    end
                 | expr as {pos = _, parent = SOME parent, typ, oper} =>
                    let do Cps.Expr.foldLabels (fn (label, ()) => selectLabel label)
                                               () oper
                        val oper = Cps.Expr.mapDefs selectDef oper
                    in Implement.expr program builder parent def typ expr
                    end
                 | {parent = NONE, ...} => raise Fail "unreachable"

            and selectDef def =
                ( if not (CpsId.HashTable.inDomain visitedDefs def)
                  then let val definiends = selectExpr def (Cps.Program.defSite program def)
                       in CpsId.HashTable.insert visitedDefs (def, definiends)
                       end
                  else ()
                ; let fun aka def =
                          case CpsId.HashTable.find visitedDefs def
                          of SOME #[def'] => if def' = def then def' else aka def'
                           | NONE => def
                           | _ => raise Fail "unreachable"
                  in aka def
                  end )

            and selectTransfer transfer label =
                let do Cps.Transfer.foldLabels (fn (label, ()) => selectLabel label)
                                               () transfer
                  (* Going right to left decreases register pressure from cont closure creation: *)
                    val transfer = Cps.Transfer.mapDefs selectDef transfer
                in Implement.transfer builder label transfer
                end

            and selectCont (label, {pos, name, cconv, tParams = _, vParams, body}) =
                ( Builder.createCont builder label {pos, name, cconv, paramTypes = vParams}
                ; Builder.setTransfer builder label (selectTransfer body label) )

            and selectLabel label =
                if not (Label.HashSetMut.member (visitedLabels, label))
                then ( Label.HashSetMut.add (visitedLabels, label)
                     ; selectCont (label, Cps.Program.labelCont program label) )
                else ()

            do selectLabel main
        in Builder.build builder main
        end
end

