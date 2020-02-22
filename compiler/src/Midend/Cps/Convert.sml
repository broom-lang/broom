functor CpsConvertFn (Abi : ABI) :> sig
    val cpsConvert : FAst.Term.program -> Cps.Program.t
end = struct
    structure FType = FAst.Type
    structure FTerm = FAst.Term
    structure Type = Cps.Type
    structure Global = Cps.Global
    structure Expr = Cps.Expr
    structure Transfer = Cps.Transfer
    structure Cont = Cps.Cont
    structure Builder = Cps.Program.Builder

    datatype typ = datatype Type.t
    datatype co = datatype Type.Coercion.co
    type def = Expr.def
    datatype oper = datatype Expr.oper
    datatype transfer = datatype Transfer.oper
    datatype pat = datatype Transfer.pat

    val op|> = Fn.|>

    datatype cont_param
        = Named of FTerm.def
        | Anon of FType.concr

    datatype cont
        = FnK of Pos.span * cont_param  * ({parent : Label.t option, stack : def, expr : def} -> Transfer.t)
        | TrivK of Pos.span * def
        | TrivlK of Pos.span * Type.t * Label.t

    structure Env = Type.Id.SortedMap (* TODO: HashMap *)

    val convertType = Cps.Type.fromF

    val rec convertCoercion =
        fn FType.Refl t => Refl (convertType t)

    fun cpsConvert {typeFns, code, sourcemap = _} =
        let val builder = Builder.new typeFns
            do Builder.insertGlobal builder ( Name.fromString "layout_Int"
                                            , Global.blobLayout Abi.Isa.Instrs.registerSize )
            do Builder.insertGlobal builder ( Name.fromString "Broom_layout_ORef"
                                            , Global.blobLayout Abi.Isa.Instrs.registerSize )
            do Builder.insertGlobal builder ( Name.fromString "layout_FnPtr"
                                            , Global.blobLayout Abi.Isa.Instrs.registerSize )
            do Builder.insertGlobal builder ( Name.fromString "layout_Box"
                                            , Global.boxLayout Abi.Isa.Instrs.registerSize )
            
            fun convertExpr parent stack cont env : FTerm.expr -> Transfer.t =
                fn expr as FTerm.Fn (f as (pos, _, _, _)) =>
                    Builder.express builder { pos, parent, typ = convertType (FTerm.typeOf expr)
                                            , oper = Label (convertFn env f) }
                    |> continue parent stack cont

                 | expr as FTerm.TFn (f as (pos, _, _)) =>
                    Builder.express builder { pos, parent, typ = convertType (FTerm.typeOf expr)
                                            , oper = Label (convertTFn env f) }
                    |> continue parent stack cont

                 | FTerm.Let (_, stmts, body) =>
                    convertBlock parent stack cont env (Vector1.Slice.full stmts) body

                 | FTerm.Letrec _ => raise Fail "unreachable"

                 | FTerm.Match (pos, _, matchee, clauses) =>
                    let val join = trivializeCont cont
                        val clauses = Vector.map (convertClause stack join env) clauses
                        val split = FnK ( pos, Anon (FTerm.typeOf matchee)
                                        , fn {parent = _, stack = _, expr} =>
                                              {pos, oper = Match (expr, clauses)} )
                    in convertExpr parent stack split env matchee
                    end

                 (* OPTIMIZE: (Via Builder?:) When callee label is known, emit goto instead of jump: *)

                 | FTerm.App (pos, _, {callee, arg}) =>
                    let val cont =
                           FnK ( FTerm.exprPos callee, Anon (FTerm.typeOf callee)
                               , fn {parent, stack, expr = callee} =>
                                     let val cont = FnK ( pos, Anon (FTerm.typeOf arg)
                                                        , fn {parent, stack, expr = arg} =>
                                                              let val ret = contValue parent cont
                                                              in { pos
                                                                 , oper = Jump { callee, tArgs = #[]
                                                                               , vArgs = #[stack, arg, ret] } }
                                                              end)
                                     in convertExpr parent stack cont env arg
                                     end)
                    in convertExpr parent stack cont env callee
                    end

                 | FTerm.TApp (pos, _, {callee, args}) =>
                    let val cont =
                            FnK ( pos, Anon (FTerm.typeOf callee)
                                , fn {parent, stack, expr = callee} =>
                                      let val tArgs = Vector1.toVector (Vector1.map convertType args)
                                          val ret = contValue parent cont
                                      in {pos, oper = Jump {callee, tArgs, vArgs = #[stack, ret]}}
                                      end )
                    in convertExpr parent stack cont env callee
                    end

                 | FTerm.PrimApp (pos, typ, opn, tArgs, vArgs, clauses) =>
                    let val tArgs = Vector.map convertType tArgs

                        fun convertArgs parent stack cont env args revArgs =
                            case VectorSlice.uncons args
                            of SOME (arg, args) =>
                                let val cont =
                                        FnK ( FTerm.exprPos arg, Anon (FTerm.typeOf arg)
                                            , fn {parent, stack, expr = arg} =>
                                                  convertArgs parent stack cont env args (arg :: revArgs) )
                                in convertExpr parent stack cont env arg
                                end
                             | NONE =>
                                let val vArgs = Vector.fromList (List.rev revArgs)
                                in  case clauses
                                    of SOME ({def = {id = successId, typ = successTyp, pos = successPos, ...}, body = success}, failure) =>
                                        let val join = trivializeCont cont
                                            val succeed = Label.fresh ()
                                            val successTyp = convertType successTyp
                                            val succeedK =
                                                let val successParam =
                                                        Builder.express builder { pos = successPos
                                                                                , parent = SOME succeed
                                                                                , typ = successTyp
                                                                                , oper = Param (succeed, 0) }
                                                    val env = Env.insert (env, successId, successParam)
                                                in { pos, name = NONE, tParams = #[], vParams = #[successTyp]
                                                   , cconv = NONE
                                                   , body = convertExpr (SOME succeed) stack join env success }
                                                end
                                            do Builder.insertCont builder (succeed, succeedK)
                                            val fail = Label.fresh ()
                                            val failK = { pos, name = NONE, tParams = #[], vParams = #[]
                                                        , cconv = NONE
                                                        , body = convertExpr (SOME fail) stack join env failure }
                                            do Builder.insertCont builder (fail, failK)
                                        in {pos, oper = Checked {opn, tArgs, vArgs, succeed, fail}}
                                        end
                                     | NONE => 
                                        let val resultTyp = convertType typ
                                            val (stack, expr) =
                                                if Primop.isTotal opn
                                                then (stack, Builder.express builder { pos, parent, typ = resultTyp
                                                                                     , oper = PrimApp {opn, tArgs, vArgs} })
                                                else let val stackT = Type.Prim Type.Prim.StackT
                                                         val resultsTyp = Results #[stackT, resultTyp]
                                                         val vArgs = VectorExt.prepend (stack, vArgs)
                                                         val results = Builder.express builder { pos, parent, typ = resultsTyp
                                                                                               , oper = PrimApp {opn, tArgs, vArgs} }
                                                     in ( Builder.express builder {pos, parent, typ = stackT, oper = Result (results, 0)}
                                                        , Builder.express builder {pos, parent, typ = resultTyp, oper = Result (results, 1)} )
                                                     end
                                        in continue parent stack cont expr
                                        end
                                end
                    in convertArgs parent stack cont env (VectorSlice.full vArgs) []
                    end

                 | FTerm.EmptyRecord pos =>
                    Builder.express builder {pos, parent, typ = Type.Record EmptyRow, oper = EmptyRecord}
                    |> continue parent stack cont
                 
                 | FTerm.With (pos, typ, {base, field = (label, fielde)}) =>
                    let val cont =
                            FnK ( FTerm.exprPos fielde, Anon (FTerm.typeOf base)
                                , fn {parent, stack, expr = base} =>
                                      let val cont =
                                              FnK ( pos, Anon (FTerm.typeOf fielde)
                                                  , fn {parent, stack, expr = fielde} =>
                                                        Builder.express builder { pos, parent
                                                                                , typ = convertType typ
                                                                                , oper = With {base, field = (label, fielde)} }
                                                        |> continue parent stack cont )
                                      in convertExpr parent stack cont env fielde
                                      end )
                    in convertExpr parent stack cont env base
                    end
 
                 | FTerm.Where (pos, typ, {base, field = (label, fielde)}) =>
                    let val cont =
                            FnK ( FTerm.exprPos fielde, Anon (FTerm.typeOf base)
                                , fn {parent, stack, expr = base} =>
                                      let val cont =
                                              FnK ( pos, Anon (FTerm.typeOf fielde)
                                                  , fn {parent, stack, expr = fielde} =>
                                                        Builder.express builder { pos, parent
                                                                                , typ = convertType typ
                                                                                , oper = Where {base, field = (label, fielde)} }
                                                        |> continue parent stack cont )
                                      in convertExpr parent stack cont env fielde
                                      end )
                    in convertExpr parent stack cont env base
                    end
 
                 | FTerm.Without (pos, typ, {base, field}) =>
                    let val cont =
                            FnK ( pos, Anon (FTerm.typeOf base)
                                , fn {parent, stack, expr = base} =>
                                      Builder.express builder { pos, parent, typ = convertType typ
                                                              , oper = Without {base, field} }
                                      |> continue parent stack cont )
                    in convertExpr parent stack cont env base
                    end

                 | FTerm.Field (pos, typ, expr, label) =>
                    let val cont =
                            FnK ( pos, Anon (FTerm.typeOf expr)
                                , fn {parent, stack, expr} =>
                                      Builder.express builder {pos, parent, typ = convertType typ, oper = Field (expr, label)}
                                      |> continue parent stack cont )
                    in convertExpr parent stack cont env expr
                    end

                 | FTerm.Cast (pos, typ, expr, co) =>
                    let val cont =
                            FnK ( pos, Anon (FTerm.typeOf expr)
                                , fn {parent, stack, expr} =>
                                      Builder.express builder { pos, parent, typ = convertType typ
                                                              , oper = Cast (expr, convertCoercion co) }
                                      |> continue parent stack cont )
                    in convertExpr parent stack cont env expr
                    end

                 | FTerm.Type (pos, t) =>
                    let val t = convertType t
                    in Builder.express builder {pos, parent, typ = Type.Type t, oper = Type t}
                       |> continue parent stack cont
                    end

                 | FTerm.Use (_, {id, ...}) => continue parent stack cont (Env.lookup (env, id))

                 | FTerm.Const (pos, c) =>
                    Builder.express builder {pos, parent, typ = Type.Prim (Const.typeOf c), oper = Const c}
                    |> continue parent stack cont

            and convertFn env (pos, {id = paramId, typ = domain, var = _, pos = paramPos}, _, body) =
                let val label = Label.fresh ()
                    val stackTyp = Type.Prim Type.Prim.StackT
                    val stack = Builder.express builder {pos, parent = SOME label, typ = stackTyp, oper = Param (label, 0)}
                    val domain = convertType domain
                    val param = Builder.express builder {pos = paramPos, parent = SOME label, typ = domain, oper = Param (label, 1)}
                    val codomain = convertType (FTerm.typeOf body)
                    val contTyp = FnT {tDomain = #[], vDomain = #[Type.Prim Type.Prim.StackT, codomain]}
                    val cont = TrivK (pos, Builder.express builder {pos, parent = SOME label, typ = contTyp, oper = Param (label, 2)})

                    val env = Env.insert (env, paramId, param)
                    val f = { pos, name = NONE (* TODO: SOME when possible *)
                            , cconv = NONE
                            , tParams = #[], vParams = #[stackTyp, domain, contTyp]
                            , body = convertExpr (SOME label) stack cont env body }
                    do Builder.insertCont builder (label, f)
                in label
                end

            and convertExportedFn (pos, params : FTerm.def vector, body) =
                let val label = Label.fresh ()
                    val parent = SOME label
                    val paramTypes =
                        Vector.mapi (fn (i, _) =>
                                         if i < Vector.length params
                                         then convertType (#typ (Vector.sub (params, i)))
                                         else Prim PrimType.Int)
                                    (#args Abi.foreignCallingConvention)
                    val calleeSaveParams =
                        Vector.map (Fn.constantly (Prim PrimType.Int))
                                   (#calleeSaves Abi.foreignCallingConvention)
                    val vParams =
                        Vector.concat [paramTypes, calleeSaveParams]
                    val paramDefs =
                        Vector.mapi (fn (i, typ) =>
                                         Builder.express builder {pos, parent, typ, oper = Param (label, i)})
                                    vParams
                    val calleeSaveArgs =
                        VectorSlice.vector (VectorSlice.slice (paramDefs, Vector.length paramTypes, NONE))
                    val stack =
                        Builder.express builder { pos, parent, typ = Prim PrimType.StackT
                                                , oper = PrimApp { opn = Primop.StackNew
                                                                 , tArgs = #[], vArgs = #[] } }
                    val retT = FTerm.typeOf body
                    val cont =
                        FnK ( pos, Anon retT
                            , fn {parent = _, stack = _, expr} =>
                                  { pos
                                  , oper = Return ( VectorExt.prepend (convertType retT, calleeSaveParams)
                                                  , VectorExt.prepend (expr, calleeSaveArgs)) } )
                    
                    val env =
                        VectorExt.zip (params, paramDefs)
                        |> Vector.foldl (fn (({id, ...}, param), env) => Env.insert (env, id, param))
                                        Env.empty
                    val f = { pos, name = NONE (* TODO: SOME when possible *)
                            , cconv = SOME CallingConvention.CCall
                            , tParams = #[], vParams
                            , body = convertExpr (SOME label) stack cont env body }
                    do Builder.insertCont builder (label, f)
                in label
                end

            and convertTFn env (pos, params, body) =
                let val label = Label.fresh ()
                    val stackTyp = Type.Prim Type.Prim.StackT
                    val stack = Builder.express builder {pos, parent = SOME label, typ = stackTyp, oper = Param (label, 0)}
                    val codomain = convertType (FTerm.typeOf body)
                    val contTyp = FnT {tDomain = #[], vDomain = #[Type.Prim Type.Prim.StackT, codomain]}
                    val cont = TrivK (pos, Builder.express builder {pos, parent = SOME label, typ = contTyp, oper = Param (label, 1)})

                    val f = { pos, name = NONE (* TODO: SOME when possible *)
                            , cconv = NONE
                            , tParams = Vector1.toVector params, vParams = #[stackTyp, contTyp]
                            , body = convertExpr (SOME label) stack cont env body }
                    do Builder.insertCont builder (label, f)
                in label
                end

            and convertBlock parent stack cont env stmts body =
                case Vector1.Slice.uncons stmts
                of SOME (stmt, stmts) =>
                    (case stmt
                     of FTerm.Val (_, def as {id, ...}, expr) =>
                         let val cont = FnK ( FTerm.stmtPos stmt, Named def
                                            , fn {parent, stack, expr} =>
                                                  let val env = Env.insert (env, id, expr)
                                                  in convertBlock parent stack cont env stmts body
                                                  end )
                         in convertExpr parent stack cont env expr
                         end
                      | FTerm.Expr expr =>
                         let val cont = FnK ( FTerm.exprPos expr, Anon (FTerm.typeOf expr)
                                            , fn {parent, stack, expr = _} =>
                                                   convertBlock parent stack cont env stmts body )
                         in convertExpr parent stack cont env expr
                         end)
                 | NONE => convertExpr parent stack cont env body

            and convertClause stack cont env {pattern, body = body} =
                let val pattern = convertPattern pattern
                    val kLabel = Label.fresh ()
                    val k = { pos = FTerm.exprPos body, name = NONE, tParams = #[], vParams = #[]
                            , cconv = NONE
                            , body = convertExpr (SOME kLabel) stack cont env body }
                    do Builder.insertCont builder (kLabel, k)
                in {pattern, target = kLabel}
                end

            and convertPattern (FTerm.AnyP _) = AnyP
              | convertPattern (FTerm.ConstP (_, c)) = ConstP c

            and continue parent stack cont expr =
                case cont
                of FnK (_, paramHint, k) => k {parent, stack, expr} (* FIXME: use `paramHint` *)
                 | TrivK (pos, k) =>
                    {pos, oper = Jump {callee = k, tArgs = #[], vArgs = #[stack, expr]}}
                 | TrivlK (pos, _, k) =>
                    {pos, oper = Goto {callee = k, tArgs = #[], vArgs = #[stack, expr]}}

            and trivializeCont cont =
                case cont
                of FnK (pos, paramHint, kf) =>
                    let val kLabel = Label.fresh ()
                        val stack = Builder.express builder { pos, parent = SOME kLabel, typ = Prim PrimType.StackT
                                                            , oper = Param (kLabel, 0) }
                        val param =
                            case paramHint
                            of Named {typ, ...} => convertType typ
                             | Anon typ => convertType typ
                        val tParams = #[]
                        val vParams = #[Type.Prim Type.Prim.StackT, param]
                        val paramUse = Builder.express builder {pos, parent = SOME kLabel, typ = param, oper = Param (kLabel, 1)}
                        val k = { pos, name = NONE, cconv = NONE, tParams, vParams
                                , body = kf {parent = SOME kLabel, stack, expr = paramUse} }
                        do Builder.insertCont builder (kLabel, k)
                    in TrivlK (pos, FnT {tDomain = tParams, vDomain = vParams}, kLabel)
                    end
                 | (TrivK _ | TrivlK _) => cont

            and contValue parent cont =
                case trivializeCont cont
                of FnK _ => raise Fail "unreachable"
                 | TrivK (_, kDef) => kDef
                 | TrivlK (pos, typ, kLabel) => Builder.express builder {pos, parent, typ, oper = Label kLabel}

            val codePos = #1 code
            val main = (codePos, #[], FTerm.Let code)
            val mainLabel = convertExportedFn main
        in Builder.build builder mainLabel
        end
end

