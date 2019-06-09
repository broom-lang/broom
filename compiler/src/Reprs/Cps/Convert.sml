structure CpsConvert :> sig
    val cpsConvert: FixedFAst.Term.expr -> Cps.Program.program
end = struct
    structure FFTerm = FixedFAst.Term
    structure CType = Cps.Type
    structure CTerm = Cps.Term
    structure Builder = Cps.Program.Builder
    type transfer = CTerm.transfer

    datatype cont = ContFn of CTerm.expr -> transfer
                  | TrivCont of CTerm.expr

    structure Env = NameSortedMap
    type env = CTerm.expr Env.map

    fun cpsConvert expr =
        let val startLabel = Label.fresh ()
            val builder = Builder.new startLabel
            
            fun convertExpr (cont: cont) (env: env) (expr: FFTerm.expr): transfer =
                raise Fail "unimplemented"

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
