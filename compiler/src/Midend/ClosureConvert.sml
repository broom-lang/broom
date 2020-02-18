functor ClosureConvertFn (Abi : ABI) :> sig
    val convert : Cps.Program.t -> Cps.Program.t
end = struct
    structure Program = Cps.Program
    structure DefMap = Program.Map
    structure LabelMap = Program.LabelMap
    structure Builder = Program.Builder
    structure Type = Cps.Type
    structure Global = Cps.Global
    structure Expr = Cps.Expr
    structure Transfer = Cps.Transfer
    structure FreeSet = CpsId.SortedSet

    type def = CpsId.t
    type label = Label.t
    datatype oper = datatype Expr.oper
    datatype transfer = datatype Transfer.t
    datatype use_site = datatype DefUses.UseSite.t

    val labelType = CpsTypechecker.labelType
    val op|> = Fn.|>

(* # Free Variables *)

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

        fun analyzeStmt program ((_, {parent = SOME parent, typ = _, oper}), frees) =
            (case oper
             of Expr.Label label =>
                 let val labelFrees = getOpt (LabelMap.find frees label, FreeSet.empty)
                 in LabelMap.update frees parent (fn
                        | SOME parentFrees => FreeSet.union (parentFrees, labelFrees)
                        | NONE => labelFrees
                    )
                 end
              | _ => Expr.foldDeps (useIn program parent) frees oper)
          | analyzeStmt _ ((_, {parent = NONE, ...}), _) = raise Fail "unreachable"

        fun analyzeStmts program stmts frees =
            DefMap.fold (analyzeStmt program) frees stmts

        fun analyzeSucc program label (target, frees) =
            let val targetFrees = getOpt (LabelMap.find frees target, FreeSet.empty)
                val targetFrees =
                    FreeSet.filter (fn def =>
                                        case Program.defSite program def
                                        of {parent = SOME parent, ...} => label <> parent
                                         | {parent = NONE, ...} => raise Fail "unreachable")
                                   targetFrees
            in LabelMap.update frees label (fn
                   | SOME labelFrees => FreeSet.union (labelFrees, targetFrees)
                   | NONE => targetFrees
               )
            end

        fun analyzeClause program label ({pattern = _, target}, frees) =
            analyzeSucc program label (target, frees)

        fun analyzeCont program ((label, {body, ...} : Cps.Cont.t), frees) =
            let val frees = LabelMap.update frees label (fn
                        | SOME labelFrees => labelFrees
                        | NONE => FreeSet.empty
                    )
                val frees =
                    case body
                    of Goto {callee, tArgs = _, vArgs = _} =>
                        let val calleeFrees = getOpt (LabelMap.find frees callee, FreeSet.empty)
                        in LabelMap.update frees label (fn
                               | SOME labelFrees => FreeSet.union (labelFrees, calleeFrees)
                               | NONE => calleeFrees
                           )
                        end
                     | Match (_, clauses) => Vector.foldl (analyzeClause program label) frees clauses
                     | Checked {opn = _, tArgs = _, vArgs = _, succeed, fail} =>
                        let val frees = analyzeSucc program label (succeed, frees)
                        in analyzeSucc program label (fail, frees)
                        end
                     | _ => frees
            in Transfer.foldlDeps (useIn program label) frees body
            end

        fun analyzeConts program conts frees =
            LabelMap.fold (analyzeCont program) frees conts

        fun iterate (program as {typeFns = _, globals = _, stmts, conts, main = _}) frees =
            let val frees' = frees
                    |> analyzeStmts program stmts
                    |> analyzeConts program conts
            in  if LabelMap.eq FreeSet.equal (frees, frees')
                then frees
                else iterate program frees'
            end

        fun analyze program = iterate program LabelMap.empty
    end

(* # Compute Goals *)

    fun align alignment offset =
        LargeWord.andb (offset + alignment - 0w1, LargeWord.notb (alignment - 0w1))

    fun typeLayoutName program =
        fn Type.FnT _ => Name.fromString "Broom_layout_ORef"
         | Type.AppT {callee = Type.Prim PrimType.Box, ...} => Name.fromString "Broom_layout_ORef"
         | Type.Prim PrimType.Int => Name.fromString "layout_Int"

    fun closureLayout program codeType cloverTypes =
        let fun step (typ, {size, alignment, revFields}) =
                let val layoutName = typeLayoutName program typ
                in  case Program.global program layoutName
                    of Global.Layout { size = SOME fieldSize
                                     , align = SOME fieldAlignment
                                     , inlineable = true
                                     , isArray = false
                                     , fields = _ } =>
                        let val offset = align (Word.toLargeWord fieldAlignment) size
                            val size = offset + fieldSize
                            val alignment = Word.max (alignment, fieldAlignment)
                            val field = {offset = SOME offset, layout = SOME layoutName}
                        in {size, alignment, revFields = field :: revFields}
                        end
                     | Global.Layout { size = _
                                     , align = _
                                     , inlineable = false
                                     , isArray = false
                                     , fields = _ } =>
                        let val fieldSize = LargeWord.fromInt Abi.Isa.Instrs.registerSize
                            val fieldAlignment = Word.fromLargeWord fieldSize
                            val offset = align (Word.toLargeWord fieldAlignment) size
                            val size = offset + fieldSize
                            val alignment = Word.max (alignment, fieldAlignment)
                            val field = {offset = SOME offset, layout = SOME layoutName}
                        in {size, alignment, revFields = field :: revFields}
                        end
                end

            val acc = (* HACK *)
                case Program.global program (Name.fromString "layout_FnPtr")
                of Global.Layout {size = SOME size, align = SOME alignment, ...} =>
                    {size, alignment, revFields = [{ offset = SOME 0w0
                                                   , layout = SOME (Name.fromString "layout_FnPtr") }]}
            val {size, alignment, revFields} = Vector.foldl step acc cloverTypes
        in Global.Layout { size = SOME size
                         , align = SOME alignment
                         , inlineable = false (* OPTIMIZE: true *)
                         , isArray = false
                         , fields = Vector.fromList (List.rev revFields) }
        end

    datatype goal
        = Lift of def vector
        | Close of Global.t * def vector
        | Split of {lift : def vector, close : label * Global.t * def vector}
        | Conditioned
        | Noop

    fun goalTransition program label labelFrees (use, goal) =
        case goal
        of SOME (Lift lift) =>
            (case use
             of Expr _ =>
                 let val layout = closureLayout program (labelType program label)
                                                (Vector.map (Program.defType program) labelFrees)
                 in SOME (Split {lift, close = (Label.fresh (), layout, labelFrees)})
                 end
              | Transfer use =>
                 (case #body (Program.labelCont program use)
                  of Goto _ => goal
                   | (Jump _ | Return _) => raise Fail "unreachable"
                   | (Checked _ | Match _) => raise Fail "unreachable: critical edge")
              | Export => raise Fail "unreachable")
         | SOME (Close (layout, clovers)) =>
            (case use
             of Expr _ => goal
              | Transfer use =>
                 (case #body (Program.labelCont program use)
                  of Goto _ => SOME (Split {lift = labelFrees, close = (Label.fresh (), layout, clovers)})
                   | (Jump _ | Return _) => raise Fail "unreachable"
                   | (Checked _ | Match _) => raise Fail "unreachable: critical edge")
              | Export => raise Fail "unreachable")
         | SOME (Split _) => goal
         | SOME (Noop | Conditioned) => raise Fail "unreachable"
         | NONE =>
            (case use
             of Expr _ =>
                 let val layout = closureLayout program (labelType program label)
                                                (Vector.map (Program.defType program) labelFrees)
                 in SOME (Close (layout, labelFrees))
                 end
              | Transfer use =>
                 (case #body (Program.labelCont program use)
                  of Goto _ => SOME (Lift labelFrees)
                   | (Jump _ | Return _) => raise Fail "unreachable"
                   | (Checked _ | Match _) => SOME Noop)
              | Export => SOME Noop)

    fun computeGoal program freeDefs ((label, uses), goals) =
        let val labelFrees = LabelMap.lookup freeDefs label
            val labelFrees = Vector.fromList (FreeSet.toList labelFrees)
            val goal = DefUses.UseSiteSet.foldl (goalTransition program label labelFrees) NONE uses
        in LabelMap.insert goals (label, valOf goal)
        end

    fun computeGoals program labelUses freeDefs =
        LabelMap.fold (computeGoal program freeDefs) LabelMap.empty labelUses

(* # Emit *)

    fun convertType t =
        case Type.mapChildren convertType t
        of Type.FnT {tDomain, vDomain} => Type.AnyClosure {tDomain, vDomain}
         | t => t

    fun closureLayoutName label = Name.fromString ("layout_Closure" ^ Label.toString label)

    fun convert (program as {typeFns, globals, stmts = _, conts = _, main}) =
        let val (_, labelUses) = DefUses.analyze program
            val freeDefs = FreeDefs.analyze program
            val goals = computeGoals program labelUses freeDefs

            val builder = Builder.new typeFns
            do Name.HashMap.appi (Builder.insertGlobal builder) globals
            val visitedLabels = Label.HashSetMut.mkEmpty 0
            val visitedDefs = CpsId.HashSetMut.mkEmpty 0

            fun convertDef program env def =
                case DefMap.find env def
                of SOME def => def
                 | NONE =>
                    if CpsId.HashSetMut.member (visitedDefs, def)
                    then def
                    else let do CpsId.HashSetMut.add (visitedDefs, def)
                             val {oper, typ, parent} = Program.defSite program def
                         in case oper
                            of Label label =>
                                (case LabelMap.lookup goals label
                                 of Close (layout, frees) =>
                                     let val layoutName = closureLayoutName label
                                         do Builder.insertGlobal builder (layoutName, layout)
                                         val oper =
                                             ClosureNew ( Builder.express builder { parent
                                                                                  , typ = Type.Prim PrimType.Layout
                                                                                  , oper = Global layoutName }
                                                        , convertLabel program label
                                                        , Vector.map (convertDef program env) frees )
                                     in Builder.insertExpr builder (def, {parent, typ = convertType typ, oper})
                                     end
                                  | Split {lift = _, close} =>
                                     let val oper = escapee program env parent (convertLabel program label) close
                                     in Builder.insertExpr builder (def, {parent, typ = convertType typ, oper})
                                     end
                                  | (Lift _ | Conditioned | Noop) => raise Fail "unreachable")
                             | PrimApp {opn, tArgs, vArgs} =>
                                let val oper = PrimApp { opn
                                                       , tArgs = Vector.map convertType tArgs
                                                       , vArgs = Vector.map (convertDef program env) vArgs }
                                in Builder.insertExpr builder (def, {oper, typ = convertType typ, parent})
                                end
                             | _ =>
                                let val oper = Expr.mapDefs (convertDef program env) oper
                                in Builder.insertExpr builder (def, {oper, typ = convertType typ, parent})
                                end
                          ; def
                         end

            and convertSucc program env label =
                let val {name, cconv, tParams, vParams, body} = Program.labelCont program label
                    val vParams = Vector.map convertType vParams
                    val body = convertTransfer program label env body
                in Builder.insertCont builder (label, {name, cconv, tParams, vParams, body})
                end

            and convertClause program env (clause as {pattern = _, target}) =
                ( convertSucc program env target
                ; clause )

            and convertTransfer program label env transfer =
                case transfer
                of Goto {callee, tArgs, vArgs} =>
                    (case LabelMap.lookup goals callee
                     of (Lift frees | Split {lift = frees, close = _}) =>
                         let val callee = convertLabel program callee
                             val vArgs = Vector.concat [vArgs, frees]
                                         |> Vector.map (convertDef program env)
                         in Goto {callee, tArgs, vArgs}
                         end
                      | (Close _ | Conditioned | Noop) => raise Fail "unreachable")
                 | Jump {callee, tArgs, vArgs} =>
                    let val closure = convertDef program env callee
                        val callee =
                            Builder.express builder { parent = SOME label
                                                    , typ = case Program.defType program callee
                                                            of Type.FnT {tDomain, vDomain} =>
                                                                let val vDomain = Vector.map convertType vDomain
                                                                in Type.FnT { tDomain
                                                                            , vDomain = VectorExt.append (vDomain, Type.Singleton closure) }
                                                                end
                                                    , oper = ClosureFn closure }
                        val vArgs = Vector.map (convertDef program env) vArgs
                    in Jump {callee, tArgs, vArgs = VectorExt.append (vArgs, closure)}
                    end
                 | Match (matchee, clauses) =>
                    let val matchee = convertDef program env matchee
                        val clauses = Vector.map (convertClause program env) clauses
                    in Match (matchee, clauses)
                    end
                 | Checked {opn, tArgs, vArgs, succeed, fail} =>
                    let val vArgs = Vector.map (convertDef program env) vArgs
                    in convertSucc program env succeed
                     ; convertSucc program env fail
                     ; Checked {opn, tArgs, vArgs, succeed, fail}
                    end
                 | Return (domain, args) =>
                    Return (domain, Vector.map (convertDef program env) args)

            and escapee program env parent label (label', layout, clovers) =
                ( if Label.HashSetMut.member (visitedLabels, label')
                  then ()
                  else let do Label.HashSetMut.add (visitedLabels, label')
                           val {name, cconv, tParams, vParams, body = _} = Program.labelCont program label
                           val closureType =
                               Type.Closure { tDomain = tParams, vDomain = vParams
                                            , clovers = Vector.map (Program.defType program) clovers }
                           val closureType = convertType closureType
                           val vParams = Vector.map convertType vParams
                           val vParams' = VectorExt.append (vParams, closureType)
                           val vArgs =
                               Vector.mapi (fn (i, typ) =>
                                                let val expr = { parent = SOME label'
                                                               , typ
                                                               , oper = Param (label', i) }
                                                in Builder.express builder expr
                                                end)
                                           vParams
                           val closureParam =
                               Builder.express builder { parent = SOME label'
                                                       , typ = closureType
                                                       , oper = Param (label', Vector.length vParams) }
                           val clovers =
                               Vector.mapi (fn (i, clover) =>
                                                  let val expr = { parent = SOME label'
                                                                 , typ = convertType (Program.defType program clover)
                                                                 , oper = Clover (closureParam, i) }
                                                  in Builder.express builder expr
                                                  end)
                                           clovers
                           val body = Goto { callee = label, tArgs = Vector.map Type.TParam tParams
                                           , vArgs = Vector.concat [vArgs, clovers] }
                       in Builder.insertCont builder (label', {name, cconv, tParams, vParams = vParams', body})
                       end
                ; let val layoutName = closureLayoutName label'
                      do Builder.insertGlobal builder (layoutName, layout)
                  in ClosureNew ( Builder.express builder {parent, typ = Type.Prim PrimType.Layout, oper = Global layoutName}
                                , label'
                                , Vector.map (convertDef program env) clovers )
                  end )

            and convertCont program (label, {name, cconv, tParams, vParams, body}) =
                case LabelMap.lookup goals label
                of (Lift frees | Split {lift = frees, close = _}) =>
                    let val oldArity = Vector.length vParams
                        val liftParams = Vector.map (Program.defType program) frees
                        val vParams = Vector.concat [vParams, liftParams]
                                      |> Vector.map convertType
                        val env =
                            Vector.foldli (fn (i, free, env) =>
                                               let val expr = { parent = SOME label
                                                              , typ = convertType (Program.defType program free)
                                                              , oper = Param (label, i + oldArity) }
                                               in DefMap.insert env (free, Builder.express builder expr)
                                               end)
                                          DefMap.empty frees
                        val body = convertTransfer program label env body
                    in Builder.insertCont builder (label, {name, cconv, tParams, vParams, body})
                    end
                 | Close (layout, frees) =>
                    let val closureType =
                            Type.Closure { tDomain = tParams, vDomain = vParams
                                         , clovers = Vector.map (Program.defType program) frees }
                        val vParams = VectorExt.append (vParams, closureType)
                                      |> Vector.map convertType
                        val closureParam =
                            Builder.express builder { parent = SOME label
                                                    , typ = convertType closureType
                                                    , oper = Param (label, Vector.length vParams - 1) }
                        val env =
                            Vector.foldli (fn (i, free, env) =>
                                               let val expr = { parent = SOME label
                                                              , typ = convertType (Program.defType program free)
                                                              , oper = Clover (closureParam, i) }
                                               in DefMap.insert env (free, Builder.express builder expr)
                                               end)
                                          DefMap.empty frees
                        val body = convertTransfer program label env body
                    in Builder.insertCont builder (label, {name, cconv, tParams, vParams, body})
                    end
                 | Conditioned => () (* Handled in `convertClause` instead. *)
                 | Noop =>
                    let val vParams = Vector.map convertType vParams
                        val body = convertTransfer program label DefMap.empty body
                    in Builder.insertCont builder (label, {name, cconv, tParams, vParams, body})
                    end

            and convertLabel program label =
                ( if not (Label.HashSetMut.member (visitedLabels, label))
                  then ( Label.HashSetMut.add (visitedLabels, label)
                       ; convertCont program (label, Program.labelCont program label) )
                  else ()
                ; label )

            do ignore (convertLabel program main)
        in Builder.build builder main
        end
end

