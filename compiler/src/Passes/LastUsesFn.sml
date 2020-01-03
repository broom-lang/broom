signature LAST_USES = sig
    structure LabelMap : HASH_MAP where type 'v t = 'v Cps.Program.LabelMap.t
    structure Isa : ISA
    structure LabelUses : LABEL_USES where type Isa.Stmt.t = Isa.Stmt.t

    type luses = CpsId.SortedSet.set

    type cont_luses = {stmts : luses vector, transfer : luses}

    type program_luses = cont_luses LabelMap.t

    val analyze : Isa.Program.t -> LabelUses.t -> program_luses
end

functor LastUsesFn (Args : sig
    structure Isa : ISA where type def = CpsId.t
    structure LabelUses : LABEL_USES where type Isa.Stmt.t = Isa.Stmt.t
end) :> LAST_USES
    where type Isa.Stmt.t = Args.Isa.Stmt.t
    where type Isa.Transfer.t = Args.Isa.Transfer.t
= struct
    structure LabelMap = Cps.Program.LabelMap
    structure Isa = Args.Isa
    structure LabelUses = Args.LabelUses

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

