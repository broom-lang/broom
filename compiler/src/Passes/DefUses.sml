structure DefUses :> sig
    structure DefMap : HASH_MAP where type key = CpsId.t
    structure LabelMap : HASH_MAP where type key = Label.t

    datatype use_site
        = Expr of CpsId.t
        | Transfer of Label.t

    val analyze : Cps.Program.t -> use_site DefMap.t * use_site LabelMap.t
end = struct
    structure DefMap = Cps.Program.Map
    structure LabelMap = Cps.Program.LabelMap

    datatype oper = datatype Cps.Expr.oper
    datatype transfer = datatype Cps.Cont.Transfer.t

    val op|> = Fn.|>

    datatype use_site
        = Expr of CpsId.t
        | Transfer of Label.t

    fun useDef (defUses, labelUses) def use =
        (DefMap.insert defUses (def, use), labelUses)

    fun useLabel (defUses, labelUses) label use =
        (defUses, LabelMap.insert labelUses (label, use))

    fun analyzeStmt ((use, {parent = _, oper}), defUses) =
        case oper
        of PrimApp {opn = _, tArgs = _, vArgs} =>
            Vector.foldl (fn (def', defUses) => useDef defUses def' (Expr use))
                         defUses vArgs
         | Where {base, field = (_, fieldDef)} | With {base, field = (_, fieldDef)} =>
            let val defUses = useDef defUses base (Expr use)
            in useDef defUses fieldDef (Expr use)
            end
         | Without {base, field = _} => useDef defUses base (Expr use)
         | Result (def, _) => useDef defUses def (Expr use)
         | Field (def, _) => useDef defUses def (Expr use)
         | Label label => useLabel defUses label (Expr use)
         | Cast (def, _) => useDef defUses def (Expr use)
         | Type _ | Param _ | EmptyRecord | Const _ => defUses

    fun analyzeStmts stmts defUses =
        DefMap.fold analyzeStmt defUses stmts

    fun analyzeCont ((use, {body, ...} : Cps.Cont.t), defUses) =
        case body
        of Goto {callee, tArgs = _, vArgs} =>
            let val defUses = useLabel defUses callee (Transfer use)
            in Vector.foldl (fn (def, defUses) => useDef defUses def (Transfer use))
                            defUses vArgs
            end
         | Jump {callee, tArgs = _, vArgs} =>
            let val defUses = useDef defUses callee (Transfer use)
            in Vector.foldl (fn (def, defUses) => useDef defUses def (Transfer use))
                            defUses vArgs
            end
         | Match (matchee, clauses) =>
            let val defUses = useDef defUses matchee (Transfer use)
            in Vector.foldl (fn ({pattern = _, target}, defUses) =>
                                 useLabel defUses target (Transfer use))
                            defUses clauses
            end

    fun analyzeConts conts defUses =
        LabelMap.fold analyzeCont defUses conts

    fun analyze {typeFns = _, stmts, conts, main = _} =
        (DefMap.empty, LabelMap.empty)
        |> analyzeStmts stmts
        |> analyzeConts conts
end

