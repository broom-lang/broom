structure ClosureConvert :> sig
    val convert : Cps.Program.t -> Cps.Program.t
end = struct
    structure Program = Cps.Program
    structure DefMap = Program.Map
    structure LabelMap = Program.LabelMap
    structure Expr = Cps.Expr
    structure Transfer = Cps.Cont.Transfer
    structure FreeSet = CpsId.SortedSet

    datatype oper = datatype Expr.oper
    datatype transfer = datatype Transfer.t

    val op|> = Fn.|>

    structure FreeDefs = struct
        fun freeDef label (def, frees) =
            LabelMap.update frees label (fn
                | SOME labelFrees => FreeSet.add (labelFrees, def)
                | NONE => FreeSet.singleton def
            )

        fun useIn program label (def, frees) =
            case Program.defSite program def
            of {parent = SOME parent, ...} =>
                if label = parent
                then frees
                else freeDef label (def, frees)
             | {parent = NONE, ...} => raise Fail "unreachable"

        fun analyzeStmt program ((_, {parent = SOME parent, oper}), frees) =
            Expr.foldDeps (useIn program parent) frees oper
          | analyzeStmt _ ((_, {parent = NONE, ...}), _) = raise Fail "unreachable"

        fun analyzeStmts program stmts frees =
            DefMap.fold (analyzeStmt program) frees stmts

        fun analyzeCont program ((label, {body, ...} : Cps.Cont.t), frees) =
            let val frees = LabelMap.update frees label (fn
                        | SOME labelFrees => labelFrees
                        | NONE => FreeSet.empty
                    )
            in Transfer.foldDeps (useIn program label) frees body
            end

        fun analyzeConts program conts frees =
            LabelMap.fold (analyzeCont program) frees conts

        fun analyze (program as {typeFns = _, stmts, conts, main = _}) =
            LabelMap.empty
            |> analyzeStmts program stmts
            |> analyzeConts program conts
    end

    fun convert program =
        let val defUses = DefUses.analyze program
            val freeDefs = FreeDefs.analyze program
        in program
        end
end

