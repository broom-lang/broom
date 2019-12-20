structure CpsConvert :> sig
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

    structure Env = FType.Id.SortedMap (* TODO: HashMap *)
    type env = def Env.map

    val convertType = Cps.Type.fromF

    val rec convertCoercion =
        fn FFType.Refl t => Refl (convertType t)

    fun cpsConvert {typeFns, code, sourcemap = _} =
        let val builder = Builder.new typeFns
            
            fun convertExpr parent stack cont env : FFTerm.expr -> transfer =
                fn FFTerm.Fn f =>
                    Builder.express builder {parent, oper = Label (convertFn parent env f)}
                    |> continue parent stack cont

                 | FFTerm.TFn f =>
                    Builder.express builder {parent, oper = Label (convertTFn parent env f)}
                    |> continue parent stack cont

                 | FFTerm.Let (_, stmts, body) =>
                    convertBlock parent stack cont env (Vector1.Slice.full stmts) body

                 | FFTerm.Letrec _ => raise Fail "unreachable"

                 | FFTerm.Match (_, _, matchee, clauses) =>
                    let val join = TrivK (trivializeCont parent cont)
                        val clauses = Vector.map (convertClause parent stack join env) clauses
                        val split = FnK ( Anon (FFTerm.typeOf matchee)
                                        , fn {parent, stack, expr} => Match (expr, clauses) )
                    in convertExpr parent stack split env matchee
                    end

                 | FFTerm.App (_, _, {callee, arg}) =>
                    let val cont =
                           FnK ( Anon (FFTerm.typeOf callee)
                               , fn {parent, stack, expr = callee} =>
                                     let val cont = FnK ( Anon (FFTerm.typeOf arg)
                                                        , fn {parent, stack, expr = arg} =>
                                                              let val ret = trivializeCont parent cont
                                                              in Goto { callee, tArgs = #[]
                                                                      , vArgs = #[stack, ret, arg] }
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
                                          val ret = trivializeCont parent cont
                                      in Goto {callee, tArgs, vArgs = #[stack, ret]}
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
                                        else let val vArgs = Vector.prepend (stack, vArgs)
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

            and convertFn parent env (_, {id = paramId, typ = domain, var = _, pos = _}, _, body) =
                let val label = Label.fresh ()
                    val stackTyp = StackT
                    val stack = Builder.express builder {parent = SOME label, oper = Param (label, 0)}
                    val codomain = convertType (FFTerm.typeOf body)
                    val contTyp = FnT {tDomain = #[], vDomain = #[StackT, codomain]}
                    val cont = TrivK (Builder.express builder {parent = SOME label, oper = Param (label, 1)})
                    val domain = convertType domain
                    val param = Builder.express builder {parent = SOME label, oper = Param (label, 2)}

                    val env = Env.insert (env, paramId, param)
                    val f = { name = NONE (* TODO: SOME when possible *)
                            , tParams = #[], vParams = #[stackTyp, contTyp, domain]
                            , body = convertExpr (SOME label) stack cont env body }
                    do Builder.insertCont builder (label, f)
                in label
                end

            and convertTFn parent env (_, params, body) =
                let val label = Label.fresh ()
                    val stackTyp = StackT
                    val stack = Builder.express builder {parent = SOME label, oper = Param (label, 0)}
                    val codomain = convertType (FFTerm.typeOf body)
                    val contTyp = FnT {tDomain = #[], vDomain = #[StackT, codomain]}
                    val cont = TrivK (Builder.express builder {parent = SOME label, oper = Param (label, 1)})

                    val f = { name = NONE (* TODO: SOME when possible *)
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

            and convertClause parent stack cont env {pattern, body} =
                let val pattern = convertPattern pattern
                    val kLabel = Label.fresh ()
                    val k = { name = NONE, tParams = #[], vParams = #[]
                            , body = convertExpr (SOME kLabel) stack cont env body }
                    do Builder.insertCont builder (kLabel, k)
                    val target = Builder.express builder {parent, oper = Label kLabel}
                in {pattern, target}
                end

            and convertPattern (FFTerm.AnyP _) = AnyP
              | convertPattern (FFTerm.ConstP (_, c)) = ConstP c

            and continue parent stack cont expr =
                case cont
                of FnK (paramHint, k) => k {parent, stack, expr} (* FIXME: use `paramHint` *)
                 | TrivK k => Goto {callee = k, tArgs = #[], vArgs = #[stack, expr]}

            and trivializeCont parent cont =
                case cont
                of FnK (paramHint, kf) =>
                    let val kLabel = Label.fresh ()
                        val stack = Builder.express builder {parent = SOME kLabel, oper = Param (kLabel, 0)}
                        val param =
                            case paramHint
                            of Named {id, typ, ...} => convertType typ
                             | Anon typ => convertType typ
                        val paramUse = Builder.express builder {parent = SOME kLabel, oper = Param (kLabel, 1)}
                        val k = { name = NONE
                                , tParams = #[], vParams = #[StackT, param]
                                , body = kf {parent = SOME kLabel, stack, expr = paramUse} }
                        do Builder.insertCont builder (kLabel, k)
                    in Builder.express builder {parent, oper = Label kLabel}
                    end
                 | TrivK kDef => kDef

            val codePos = #1 code
            val mainParam = { pos = codePos, id = DefId.fresh (), var = Name.fresh ()
                            , typ = FFType.Record FFType.EmptyRow }
            val main = (codePos, mainParam, Cst.Explicit FType.Impure, FFTerm.Let code)
            val mainLabel = convertFn NONE Env.empty main
        in Builder.build builder mainLabel
        end
end

