functor CpsConvertFn (Abi : ABI) :> sig
    val cpsConvert : FixedFAst.Term.program -> Cps.Program.t
end = struct
    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term
    structure Type = Cps.Type
    structure Expr = Cps.Expr
    structure Cont = Cps.Cont
    structure Builder = Cps.Program.Builder

    datatype typ = datatype Type.t
    datatype co = datatype Type.Coercion.co
    type def = Expr.def
    datatype oper = datatype Expr.oper
    datatype transfer = datatype Cont.Transfer.t
    datatype pat = datatype Cont.Transfer.pat

    val op|> = Fn.|>

    datatype cont_param
        = Named of FFTerm.def
        | Anon of FFType.concr

    datatype cont
        = FnK of cont_param  * ({parent : Label.t option, stack : def, expr : def} -> transfer)
        | TrivK of def
        | TrivlK of Label.t

    structure Env = FType.Id.SortedMap (* TODO: HashMap *)

    val convertType = Cps.Type.fromF

    val rec convertCoercion =
        fn FFType.Refl t => Refl (convertType t)

    fun cpsConvert {typeFns, code, sourcemap = _} =
        let val builder = Builder.new typeFns
            
            fun convertExpr parent stack cont env : FFTerm.expr -> transfer =
                fn FFTerm.Fn f =>
                    Builder.express builder {parent, oper = Label (convertFn env f)}
                    |> continue parent stack cont

                 | FFTerm.TFn f =>
                    Builder.express builder {parent, oper = Label (convertTFn env f)}
                    |> continue parent stack cont

                 | FFTerm.Let (_, stmts, body) =>
                    convertBlock parent stack cont env (Vector1.Slice.full stmts) body

                 | FFTerm.Letrec _ => raise Fail "unreachable"

                 | FFTerm.Match (_, _, matchee, clauses) =>
                    let val join = trivializeCont cont
                        val clauses = Vector.map (convertClause stack join env) clauses
                        val split = FnK ( Anon (FFTerm.typeOf matchee)
                                        , fn {parent = _, stack = _, expr} => Match (expr, clauses) )
                    in convertExpr parent stack split env matchee
                    end

                 (* OPTIMIZE: (Via Builder?:) When callee label is known, emit goto instead of jump: *)

                 | FFTerm.App (_, _, {callee, arg}) =>
                    let val cont =
                           FnK ( Anon (FFTerm.typeOf callee)
                               , fn {parent, stack, expr = callee} =>
                                     let val cont = FnK ( Anon (FFTerm.typeOf arg)
                                                        , fn {parent, stack, expr = arg} =>
                                                              let val ret = contValue parent cont
                                                              in Jump { callee, tArgs = #[]
                                                                      , vArgs = #[stack, arg, ret] }
                                                              end)
                                     in convertExpr parent stack cont env arg
                                     end)
                    in convertExpr parent stack cont env callee
                    end

                 | FFTerm.TApp (_, _, {callee, args}) =>
                    let val cont =
                            FnK ( Anon (FFTerm.typeOf callee)
                                , fn {parent, stack, expr = callee} =>
                                      let val tArgs = Vector1.toVector (Vector1.map convertType args)
                                          val ret = contValue parent cont
                                      in Jump {callee, tArgs, vArgs = #[stack, ret]}
                                      end )
                    in convertExpr parent stack cont env callee
                    end

                 | FFTerm.PrimApp (_, _, opn, tArgs, vArgs) =>
                    let val tArgs = Vector.map convertType tArgs

                        fun convertArgs parent stack cont env args revArgs =
                            case VectorSlice.uncons args
                            of SOME (arg, args) =>
                                let val cont =
                                        FnK ( Anon (FFTerm.typeOf arg)
                                            , fn {parent, stack, expr = arg} =>
                                                  convertArgs parent stack cont env args (arg :: revArgs) )
                                in convertExpr parent stack cont env arg
                                end
                             | NONE =>
                                let val vArgs = Vector.fromList (List.rev revArgs)
                                    val (stack, expr) =
                                        if Primop.isTotal opn
                                        then (stack, Builder.express builder {parent, oper = PrimApp {opn, tArgs, vArgs}})
                                        else let val vArgs = VectorExt.prepend (stack, vArgs)
                                                 val results = Builder.express builder {parent, oper = PrimApp {opn, tArgs, vArgs}}
                                             in ( Builder.express builder {parent, oper = Result (results, 0)}
                                                , Builder.express builder {parent, oper = Result (results, 1)} )
                                             end
                                in continue parent stack cont expr
                                end
                    in convertArgs parent stack cont env (VectorSlice.full vArgs) []
                    end

                 | FFTerm.EmptyRecord _ =>
                    Builder.express builder {parent, oper = EmptyRecord}
                    |> continue parent stack cont
                 
                 | FFTerm.With (_, _, {base, field = (label, fielde)}) =>
                    let val cont =
                            FnK ( Anon (FFTerm.typeOf base)
                                , fn {parent, stack, expr = base} =>
                                      let val cont =
                                              FnK ( Anon (FFTerm.typeOf fielde)
                                                  , fn {parent, stack, expr = fielde} =>
                                                        Builder.express builder { parent
                                                                                , oper = With {base, field = (label, fielde)} }
                                                        |> continue parent stack cont )
                                      in convertExpr parent stack cont env fielde
                                      end )
                    in convertExpr parent stack cont env base
                    end
 
                 | FFTerm.Where (_, _, {base, field = (label, fielde)}) =>
                    let val cont =
                            FnK ( Anon (FFTerm.typeOf base)
                                , fn {parent, stack, expr = base} =>
                                      let val cont =
                                              FnK ( Anon (FFTerm.typeOf fielde)
                                                  , fn {parent, stack, expr = fielde} =>
                                                        Builder.express builder { parent
                                                                                , oper = Where {base, field = (label, fielde)} }
                                                        |> continue parent stack cont )
                                      in convertExpr parent stack cont env fielde
                                      end )
                    in convertExpr parent stack cont env base
                    end
 
                 | FFTerm.Without (_, _, {base, field}) =>
                    let val cont =
                            FnK ( Anon (FFTerm.typeOf base)
                                , fn {parent, stack, expr = base} =>
                                      Builder.express builder {parent, oper = Without {base, field}}
                                      |> continue parent stack cont )
                    in convertExpr parent stack cont env base
                    end

                 | FFTerm.Field (_, _, expr, label) =>
                    let val cont =
                            FnK ( Anon (FFTerm.typeOf expr)
                                , fn {parent, stack, expr} =>
                                      Builder.express builder {parent, oper = Field (expr, label)}
                                      |> continue parent stack cont )
                    in convertExpr parent stack cont env expr
                    end

                 | FFTerm.Cast (_, _, expr, co) =>
                    let val cont =
                            FnK ( Anon (FFTerm.typeOf expr)
                                , fn {parent, stack, expr} =>
                                      Builder.express builder {parent, oper = Cast (expr, convertCoercion co)}
                                      |> continue parent stack cont )
                    in convertExpr parent stack cont env expr
                    end

                 | FFTerm.Type (_, t) =>
                    Builder.express builder {parent, oper = Type (convertType t)}
                    |> continue parent stack cont

                 | FFTerm.Use (_, {id, ...}) => continue parent stack cont (Env.lookup (env, id))

                 | FFTerm.Const (_, c) =>
                    Builder.express builder {parent, oper = Const c}
                    |> continue parent stack cont

            and convertFn env (_, {id = paramId, typ = domain, var = _, pos = _}, _, body) =
                let val label = Label.fresh ()
                    val stackTyp = Type.Prim Type.Prim.StackT
                    val stack = Builder.express builder {parent = SOME label, oper = Param (label, 0)}
                    val domain = convertType domain
                    val param = Builder.express builder {parent = SOME label, oper = Param (label, 1)}
                    val codomain = convertType (FFTerm.typeOf body)
                    val contTyp = FnT {tDomain = #[], vDomain = #[Type.Prim Type.Prim.StackT, codomain]}
                    val cont = TrivK (Builder.express builder {parent = SOME label, oper = Param (label, 2)})

                    val env = Env.insert (env, paramId, param)
                    val f = { name = NONE (* TODO: SOME when possible *)
                            , cconv = NONE
                            , tParams = #[], vParams = #[stackTyp, domain, contTyp]
                            , body = convertExpr (SOME label) stack cont env body }
                    do Builder.insertCont builder (label, f)
                in label
                end

            and convertExportedFn (_, params : FFTerm.def vector, body) =
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
                        Vector.mapi (fn (i, _) =>
                                         Builder.express builder {parent, oper = Param (label, i)})
                                    vParams
                    val calleeSaveArgs =
                        VectorSlice.vector (VectorSlice.slice (paramDefs, Vector.length paramTypes, NONE))
                    val stack =
                        Builder.express builder { parent
                                                , oper = PrimApp { opn = Primop.StackNew
                                                                 , tArgs = #[], vArgs = #[] } }
                    val retT = FFTerm.typeOf body
                    val cont =
                        FnK ( Anon retT
                            , fn {parent = _, stack = _, expr} =>
                                  Return ( VectorExt.prepend (convertType retT, calleeSaveParams)
                                         , VectorExt.prepend (expr, calleeSaveArgs)) )
                    
                    val env =
                        VectorExt.zip (params, paramDefs)
                        |> Vector.foldl (fn (({id, ...}, param), env) => Env.insert (env, id, param))
                                        Env.empty
                    val f = { name = NONE (* TODO: SOME when possible *)
                            , cconv = SOME CallingConvention.CCall
                            , tParams = #[], vParams
                            , body = convertExpr (SOME label) stack cont env body }
                    do Builder.insertCont builder (label, f)
                in label
                end

            and convertTFn env (_, params, body) =
                let val label = Label.fresh ()
                    val stackTyp = Type.Prim Type.Prim.StackT
                    val stack = Builder.express builder {parent = SOME label, oper = Param (label, 0)}
                    val codomain = convertType (FFTerm.typeOf body)
                    val contTyp = FnT {tDomain = #[], vDomain = #[Type.Prim Type.Prim.StackT, codomain]}
                    val cont = TrivK (Builder.express builder {parent = SOME label, oper = Param (label, 1)})

                    val f = { name = NONE (* TODO: SOME when possible *)
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
                     of FFTerm.Val (_, def as {id, ...}, expr) =>
                         let val cont = FnK ( Named def
                                            , fn {parent, stack, expr} =>
                                                  let val env = Env.insert (env, id, expr)
                                                  in convertBlock parent stack cont env stmts body
                                                  end )
                         in convertExpr parent stack cont env expr
                         end
                      | FFTerm.Expr expr =>
                         let val cont = FnK ( Anon (FFTerm.typeOf expr)
                                            , fn {parent, stack, expr = _} =>
                                                   convertBlock parent stack cont env stmts body )
                         in convertExpr parent stack cont env expr
                         end)
                 | NONE => convertExpr parent stack cont env body

            and convertClause stack cont env {pattern, body} =
                let val pattern = convertPattern pattern
                    val kLabel = Label.fresh ()
                    val k = { name = NONE, tParams = #[], vParams = #[]
                            , cconv = NONE
                            , body = convertExpr (SOME kLabel) stack cont env body }
                    do Builder.insertCont builder (kLabel, k)
                in {pattern, target = kLabel}
                end

            and convertPattern (FFTerm.AnyP _) = AnyP
              | convertPattern (FFTerm.ConstP (_, c)) = ConstP c

            and continue parent stack cont expr =
                case cont
                of FnK (paramHint, k) => k {parent, stack, expr} (* FIXME: use `paramHint` *)
                 | TrivK k => Jump {callee = k, tArgs = #[], vArgs = #[stack, expr]}
                 | TrivlK k => Goto {callee = k, tArgs = #[], vArgs = #[stack, expr]}

            and trivializeCont cont =
                case cont
                of FnK (paramHint, kf) =>
                    let val kLabel = Label.fresh ()
                        val stack = Builder.express builder {parent = SOME kLabel, oper = Param (kLabel, 0)}
                        val param =
                            case paramHint
                            of Named {typ, ...} => convertType typ
                             | Anon typ => convertType typ
                        val paramUse = Builder.express builder {parent = SOME kLabel, oper = Param (kLabel, 1)}
                        val k = { name = NONE, cconv = NONE
                                , tParams = #[], vParams = #[Type.Prim Type.Prim.StackT, param]
                                , body = kf {parent = SOME kLabel, stack, expr = paramUse} }
                        do Builder.insertCont builder (kLabel, k)
                    in TrivlK kLabel
                    end
                 | (TrivK _ | TrivlK _) => cont

            and contValue parent cont =
                case trivializeCont cont
                of FnK _ => raise Fail "unreachable"
                 | TrivK kDef => kDef
                 | TrivlK kLabel => Builder.express builder {parent, oper = Label kLabel}

            val codePos = #1 code
            val main = (codePos, #[], FFTerm.Let code)
            val mainLabel = convertExportedFn main
        in Builder.build builder mainLabel
        end
end

