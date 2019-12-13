structure CpsConvert :> sig
    val cpsConvert : FixedFAst.Term.program -> Cps.Program.t
end = struct
    fun cpsConvert program = raise Fail "unimplemented"
end

(*structure CpsConvert :> sig
    val cpsConvert: FixedFAst.Term.expr -> Cps.Program.program
end = struct
    type 'a slice = 'a VectorSlice.slice

    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term
    structure CType = Cps.Type
    structure CTerm = Cps.Term
    structure Builder = Cps.Program.Builder
    datatype transfer = datatype CTerm.transfer

    datatype param_hint = Exactly of CTerm.param
                        | Fresh of CType.typ
                        | Anon of CType.typ

    datatype cont = ContFn of param_hint * (CTerm.expr -> transfer)
                  | TrivCont of CTerm.expr

    val expectedName =
        fn ContFn (Exactly {var, typ = _}, _) => SOME var
         | _ => NONE

    structure Env = NameSortedMap
    type env = CTerm.expr Env.map

    fun convertType (FFType.Fix typ) =
        case typ
        of FFType.Arrow (_, {domain, codomain}) =>
            CType.FnT { typeParams = Vector.fromList []
                      , paramTypes = Vector.fromList [ CType.cont (convertType codomain)
                                                     , convertType domain ] }
         | FFType.Prim (_, p) => CType.Prim p

    (* FIXME: Impure statements should be retained even when their values are unused. *)

    fun cpsConvert expr =
        let val startLabel = Label.fresh ()
            val builder = Builder.new startLabel
            
            fun convertExpr (cont: cont) (env: env): FFTerm.expr -> transfer =
                fn FFTerm.Fn (_, {var, typ}, body) =>
                    let val label = Label.fresh ()
                        val param = {var, typ = convertType typ}
                        val domain = convertType (FFTerm.typeOf body)
                        val retParam = { var = Name.fresh ()
                                       , typ = CType.cont domain }
                        val ret = TrivCont (CTerm.newExpr (CTerm.Param retParam))
                        val f = { name = Option.unwrapOrElse (expectedName cont) Name.fresh
                                , typeParams = Vector.fromList []
                                , valParams = Vector.fromList [retParam, param]
                                , body = let val env = Env.insert (env, var, CTerm.newExpr (CTerm.Param param))
                                         in convertExpr ret env body
                                         end }
                        do Builder.insertCont (builder, label, f)
                    in continue cont (CTerm.newExpr (CTerm.Label label))
                    end
                 | FFTerm.App (_, _, {callee, arg}) =>
                    let val cont = ContFn ( Fresh (convertType (FFTerm.typeOf callee))
                                          , fn callee =>
                                                let val cont = ContFn ( Fresh (convertType (FFTerm.typeOf arg))
                                                                      , fn arg =>
                                                                            let val ret = trivializeCont cont
                                                                            in Goto (callee, Vector.fromList [],
                                                                                     Vector.fromList [ret, arg])
                                                                            end)
                                                in convertExpr cont env arg
                                                end)
                    in convertExpr cont env callee
                    end
                 | FFTerm.Let (_, stmts, body) =>
                    convertBlock cont env (VectorSlice.full stmts) body
                 | FFTerm.If (_, cond, conseq, alt) =>
                    let val join = TrivCont (trivializeCont cont)
                        val conseq = CTerm.newExpr (CTerm.Label (exprLabel join env conseq))
                        val alt = CTerm.newExpr (CTerm.Label (exprLabel join env alt))
                        val split = ContFn ( Fresh (convertType (FFTerm.typeOf cond))
                                           , fn cond => If (cond, conseq, alt) )
                    in convertExpr split env cond
                    end
                 | FFTerm.Use (_, {var, ...}) => continue cont (Env.lookup (env, var))
                 | FFTerm.Const (_, c) => continue cont (CTerm.newExpr (CTerm.Const c))

            and exprLabel (cont: cont) (env: env) (expr: FFTerm.expr) =
                let val label = Label.fresh ()
                    val cont = { name = Name.fresh ()
                               , typeParams = Vector.fromList []
                               , valParams = Vector.fromList []
                               , body = convertExpr cont env expr }
                    do Builder.insertCont (builder, label, cont)
                in label
                end

            and convertBlock (cont: cont) (env: env) (stmts: FFType.typ FFTerm.stmt slice) (body: FFTerm.expr): transfer =
                case VectorSlice.uncons stmts
                of SOME (stmt, stmts) =>
                    (case stmt
                     of FFTerm.Val (_, {var, typ}, expr) =>
                         let val param = {var, typ = convertType typ}
                             val cont = ContFn ( Exactly param
                                               , fn expr =>
                                                     let val env = Env.insert (env, var, expr)
                                                     in convertBlock cont env stmts body
                                                     end)
                         in convertExpr cont env expr
                         end
                      | FFTerm.Expr expr =>
                         let val cont = ContFn ( Anon (convertType (FFTerm.typeOf expr))
                                               , fn expr => convertBlock cont env stmts body )
                         in convertExpr cont env expr
                         end)
                 | NONE => convertExpr cont env body

            and continue (cont: cont) (expr: CTerm.expr): transfer =
                case cont
                of ContFn (_, kf) => kf expr
                 | TrivCont kexpr => Goto (kexpr, Vector.fromList [], Vector.fromList [expr])

            and trivializeCont cont =
                case cont
                of ContFn (paramHint, kf) =>
                    let val label = Label.fresh ()
                        val param = case paramHint
                                    of Exactly param => param
                                     | Fresh typ | Anon typ => {var = Name.fresh (), typ}
                        val cont = { name = Name.freshen (Name.fromString "k")
                                   , typeParams = Vector.fromList []
                                   , valParams = Vector.fromList [param]
                                   , body = kf (CTerm.newExpr (CTerm.Param param)) }
                        do Builder.insertCont (builder, label, cont)
                    in CTerm.newExpr (CTerm.Label label)
                    end
                 | TrivCont kexpr => kexpr

            val retParam = {var = Name.fresh (), typ = CType.cont CType.int}
            val ret = TrivCont (CTerm.newExpr (CTerm.Param retParam))
            val startCont = { name = Name.fromString "__start"
                            , typeParams = Vector.fromList []
                            , valParams = Vector.fromList [retParam]
                            , body = convertExpr ret Env.empty expr }
            do Builder.insertCont (builder, startLabel, startCont)
        in Builder.build builder
        end
end*)
