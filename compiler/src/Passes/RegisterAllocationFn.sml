functor RegisterAllocationFn (Args : sig
    structure Isa : ISA where type def = CpsId.t
    structure RegIsa : ISA
end) :> sig
    val allocate : Args.Isa.Program.t -> Args.RegIsa.Program.t
end = struct
    structure Isa = Args.Isa
    structure LabelMap = Cps.Program.LabelMap
    structure Builder = Args.RegIsa.Program.Builder
    structure LabelUses = IsaLabelUsesFn(Args.Isa)

    structure LastUses = struct
        type luses = CpsId.SortedSet.set

        type cont_luses = {stmts : luses vector, transfer : luses}

        type program_luses = cont_luses LabelMap.t

        fun initialContLuses {name = _, argc = _, stmts, transfer = _} =
            { stmts = Vector.tabulate ( Vector.length stmts
                                      , Fn.constantly CpsId.SortedSet.empty )
            , transfer = CpsId.SortedSet.empty }

        fun analyze (program as {conts, main = _}) useCounts =
            let val luses = ref (LabelMap.map initialContLuses conts)

                fun transferLuse label def =
                    luses := LabelMap.update (!luses) label (fn
                        | SOME {stmts, transfer} =>
                           {stmts, transfer = CpsId.SortedSet.add (transfer, def)}
                        | NONE => raise Fail "unreachable"
                    )

                fun stmtLuse label i def =
                    luses := LabelMap.update (!luses) label (fn
                        | SOME {stmts, transfer} =>
                           { stmts = Vector.update (stmts, i, CpsId.SortedSet.add (Vector.sub (stmts, i), def))
                           , transfer }
                        | NONE => raise Fail "unreachable"
                    )

                fun analyzeDef luse (def, succsFrees) =
                    if CpsId.SortedSet.member (succsFrees, def)
                    then succsFrees
                    else ( luse def
                         ; CpsId.SortedSet.add (succsFrees, def) )

                fun analyzeExpr label i =
                    Isa.Instrs.Oper.foldDefs (analyzeDef (stmtLuse label i))

                fun analyzeStmt label (i, stmt, succsFrees) =
                    case stmt
                    of Isa.Stmt.Def (def, expr) =>
                        let val succsFrees = analyzeExpr label i succsFrees expr
                        in analyzeDef (stmtLuse label i) (def, succsFrees)
                        end
                     | Isa.Stmt.Eff expr => analyzeExpr label i succsFrees expr
                     | Isa.Stmt.Param (def, _, _) =>
                        analyzeDef (stmtLuse label i) (def, succsFrees)

                fun analyzeSucc label =
                    let val {calls, ...} = LabelMap.lookup useCounts label
                    in  if calls = 1
                        then analyzeEBB label (LabelMap.lookup conts label)
                        else CpsId.SortedSet.empty
                    end

                and analyzeTransfer label transfer =
                    let val succsFrees =
                            Isa.Instrs.Transfer.foldLabels (fn (label, succsFrees) =>
                                                                let val succFrees = analyzeSucc label
                                                                in CpsId.SortedSet.union (succsFrees, succFrees)
                                                                end)
                                                           CpsId.SortedSet.empty transfer
                    in Isa.Instrs.Transfer.foldDefs (analyzeDef (transferLuse label)) succsFrees transfer
                    end

                and analyzeEBB label {name = _, argc = _, stmts, transfer} =
                    let val transferFrees = analyzeTransfer label transfer
                    in Vector.foldri (analyzeStmt label) transferFrees stmts
                    end

                fun analyzeCont (label, cont) =
                    let val {exports, escapes, calls} = LabelMap.lookup useCounts label
                    in  if exports > 0 orelse escapes > 0 orelse calls > 1
                        then ignore (analyzeEBB label cont)
                        else ()
                    end
                
                do LabelMap.appi analyzeCont conts
            in !luses
            end
    end

    fun allocate program =
        let val useCounts = LabelUses.useCounts program
            val lastUses = LastUses.analyze program useCounts
            
            val callingConventions = Label.HashTable.mkTable (0, Subscript)
            val builder = Builder.new ()
        in raise Fail "unimplemented"
        end
end

