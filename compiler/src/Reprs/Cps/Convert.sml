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
    type def = Expr.def
    datatype oper = datatype Expr.oper
    datatype transfer = datatype Cont.Transfer.t
    datatype pat = datatype Cont.Transfer.pat

    datatype cont_param
        = Named of FFTerm.def
        | Anon of FFType.concr

    datatype cont
        = FnK of cont_param  * ({parent : Label.t option, stack : def, expr : def} -> transfer)
        | TrivK of def

    structure Env = FType.Id.SortedMap (* TODO: HashMap *)
    type env = def Env.map

    val rec convertType =
        fn FFType.Arrow (_, {domain, codomain}) =>
            let val contTyp = FnT {tDomain = #[], vDomain = #[StackT, convertType codomain]}
            in FnT {tDomain = #[], vDomain = #[StackT, contTyp, convertType domain]}
            end
         | FFType.ForAll (params, body) =>
            let val contTyp = FnT {tDomain = #[], vDomain = #[StackT, convertType body]}
            in FnT {tDomain = Vector1.toVector params, vDomain = #[StackT, contTyp]}
            end
         | FFType.Record row => Record (convertType row)
         | FFType.EmptyRow => EmptyRow
         | FFType.Type t => Cps.Type.Type (convertType t)
         | FFType.UseT def => TParam def
         | FFType.Prim p => Prim p

    fun cpsConvert {typeFns, stmts, sourcemap = _} =
        let val builder = Builder.new typeFns
            
            fun convertExpr parent stack cont env : FFTerm.expr -> transfer =
                fn FFTerm.Fn f =>
                    continue parent stack cont (Builder.label builder parent (convertFn parent env f))

                 | FFTerm.TFn f =>
                    continue parent stack cont (Builder.label builder parent (convertTFn parent env f))

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

                 | FFTerm.Type (_, t) =>
                    continue parent stack cont (Builder.typ builder parent (convertType t))

                 | FFTerm.Use (_, {id, ...}) => continue parent stack cont (Env.lookup (env, id))

                 | FFTerm.Const (_, c) =>
                    continue parent stack cont (Builder.const builder parent c)

            and convertFn parent env (_, {id = paramId, typ = domain, var = _, pos = _}, _, body) =
                let val label = Label.fresh ()
                    val stackTyp = StackT
                    val stack = Builder.param builder (SOME label) label 0
                    val codomain = convertType (FFTerm.typeOf body)
                    val contTyp = FnT {tDomain = #[], vDomain = #[StackT, codomain]}
                    val cont = TrivK (Builder.param builder (SOME label) label 1)
                    val domain = convertType domain
                    val param = Builder.param builder (SOME label) label 2

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
                    val stack = Builder.param builder (SOME label) label 0
                    val codomain = convertType (FFTerm.typeOf body)
                    val contTyp = FnT {tDomain = #[], vDomain = #[StackT, codomain]}
                    val cont = TrivK (Builder.param builder (SOME label) label 1)

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
                in {pattern, target = Builder.label builder parent kLabel}
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
                        val stack = Builder.param builder (SOME kLabel) kLabel 0
                        val param =
                            case paramHint
                            of Named {id, typ, ...} => convertType typ
                             | Anon typ => convertType typ
                        val paramUse = Builder.param builder (SOME kLabel) kLabel 1
                        val k = { name = NONE
                                , tParams = #[], vParams = #[StackT, param]
                                , body = kf {parent = SOME kLabel, stack, expr = paramUse} }
                        do Builder.insertCont builder (kLabel, k)
                    in Builder.label builder parent kLabel
                    end
                 | TrivK kDef => kDef

            val startPos = FFTerm.stmtPos (Vector.sub (stmts, 0))
            val endPos = FFTerm.stmtPos (Vector.sub (stmts, Vector.length stmts - 1))
            val mainParam = { pos = startPos, id = DefId.fresh (), var = Name.fresh ()
                            , typ = FFType.Record FFType.EmptyRow }
            val main =
                ( startPos, mainParam, Cst.Explicit FType.Impure
                , FFTerm.Let ( startPos, valOf (Vector1.fromVector stmts)
                             , FFTerm.Const (endPos, Const.Int 0) ) )
            val mainLabel = convertFn NONE Env.empty main
        in Builder.build builder mainLabel
        end
end

