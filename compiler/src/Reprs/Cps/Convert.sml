structure CpsConvert :> sig
    val cpsConvert: FixedFAst.Term.expr -> Cps.Program.program
end = struct
    type 'a slice = 'a VectorSlice.slice

    structure FFType = FixedFAst.Type
    structure FFTerm = FixedFAst.Term
    structure CType = Cps.Type
    structure CTerm = Cps.Term
    structure Builder = Cps.Program.Builder
    type transfer = CTerm.transfer

    datatype cont = ContFn of CTerm.expr -> transfer
                  | TrivCont of CTerm.expr

    structure Env = NameSortedMap
    type env = CTerm.expr Env.map

    (* FIXME: Impure statements should be retained even when their values are unused. *)

    fun cpsConvert expr =
        let val startLabel = Label.fresh ()
            val builder = Builder.new startLabel
            
            fun convertExpr (cont: cont) (env: env): FFTerm.expr -> transfer =
                fn FFTerm.Let (_, stmts, body) =>
                    convertBlock cont env (VectorSlice.full stmts) body
                 | FFTerm.Const (_, c) =>
                    continue cont (CTerm.newExpr (CTerm.Const c))

            and convertBlock (cont: cont) (env: env) (stmts: FFType.typ FFTerm.stmt slice) (body: FFTerm.expr): transfer =
                case VectorSlice.uncons stmts
                of SOME (stmt, stmts) =>
                    (case stmt
                     of FFTerm.Val (_, {var, typ}, expr) =>
                         let val cont = ContFn (fn expr =>
                                                    let val env = Env.insert (env, var, expr)
                                                    in convertBlock cont env stmts body
                                                    end)
                         in convertExpr cont env expr
                         end
                      | FFTerm.Expr expr =>
                         let val cont = ContFn (fn expr => convertBlock cont env stmts body)
                         in convertExpr cont env expr
                         end)
                 | NONE => convertExpr cont env body

            and continue (cont: cont) (expr: CTerm.expr): transfer =
                case cont
                of ContFn kf => kf expr

            val retParam = {var = Name.fresh (), typ = CType.cont CType.int}
            val ret = TrivCont (CTerm.newExpr (CTerm.Param retParam))
            val startCont = { name = Name.fromString "__start"
                            , typeParams = Vector.fromList []
                            , valParams = Vector.fromList [retParam]
                            , body = convertExpr ret Env.empty expr }
            do Builder.insertCont (builder, startLabel, startCont)
        in Builder.build builder
        end
end
