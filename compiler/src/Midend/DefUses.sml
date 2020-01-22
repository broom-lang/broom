structure DefUses :> sig
    structure DefMap : HASH_MAP where type key = CpsId.t
    structure LabelMap : HASH_MAP
        where type key = Label.t
        where type 'v t = 'v Cps.Program.LabelMap.t

    structure UseSite : sig
        datatype t
            = Expr of CpsId.t
            | Transfer of Label.t
            | Export

        val compare : t * t -> order
    end

    structure UseSiteSet : ORD_SET where type Key.ord_key = UseSite.t

    val analyze : Cps.Program.t -> UseSiteSet.set DefMap.t * UseSiteSet.set LabelMap.t
end = struct
    structure DefMap = Cps.Program.Map
    structure LabelMap = Cps.Program.LabelMap

    datatype oper = datatype Cps.Expr.oper
    datatype transfer = datatype Cps.Transfer.t

    val op|> = Fn.|>

    structure UseSite = struct
        datatype t
            = Expr of CpsId.t
            | Transfer of Label.t
            | Export

        type ord_key = t

        val compare =
            fn (Expr def, Expr def') => CpsId.compare (def, def')
             | (Expr _, Transfer _) => LESS
             | (Transfer _, Expr _) => GREATER
             | (Transfer label, Transfer label') => Label.compare (label, label')
    end

    datatype use_site = datatype UseSite.t

    structure UseSiteSet = BinarySetFn(UseSite)

    fun useDef (defUses, labelUses) def use =
        ( DefMap.update defUses def (fn
              | SOME uses => UseSiteSet.add (uses, use)
              | NONE => UseSiteSet.singleton use
          )
        , labelUses )

    fun useLabel (defUses, labelUses) label use =
        ( defUses
        , LabelMap.update labelUses label (fn
              | SOME uses => UseSiteSet.add (uses, use)
              | NONE => UseSiteSet.singleton use
          ) )

    fun analyzeStmt ((use, {parent = _, oper}), defUses) =
        case oper
        of PrimApp {opn = _, tArgs = _, vArgs} =>
            Vector.foldl (fn (def', defUses) => useDef defUses def' (Expr use))
                         defUses vArgs
         | (Where {base, field = (_, fieldDef)} | With {base, field = (_, fieldDef)}) =>
            let val defUses = useDef defUses base (Expr use)
            in useDef defUses fieldDef (Expr use)
            end
         | Without {base, field = _} => useDef defUses base (Expr use)
         | Result (def, _) => useDef defUses def (Expr use)
         | Field (def, _) => useDef defUses def (Expr use)
         | Label label => useLabel defUses label (Expr use)
         | Cast (def, _) => useDef defUses def (Expr use)
         | (Type _ | Param _ | EmptyRecord | Const _) => defUses

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
         | Checked {opn = _, tArgs = _, vArgs, succeed, fail} =>
            let val defUses = Vector.foldl (fn (def, defUses) => useDef defUses def (Transfer use))
                                           defUses vArgs
                val defUses = useLabel defUses succeed (Transfer use)
            in useLabel defUses fail (Transfer use)
            end
         | Return (_, args) =>
            Vector.foldl (fn (def, defUses) => useDef defUses def (Transfer use))
                         defUses args

    fun analyzeConts conts defUses =
        LabelMap.fold analyzeCont defUses conts

    fun analyze {typeFns = _, stmts, conts, main} =
        (DefMap.empty, LabelMap.insert LabelMap.empty (main, UseSiteSet.singleton Export))
        |> analyzeStmts stmts
        |> analyzeConts conts
end

