structure CPSConvert :> sig
    val cpsConvert: FAst.Term.stmt vector -> CPS.Term.expr
end = struct
    datatype t = datatype CPS.Type.t
    datatype expr = datatype CPS.Term.expr

    datatype cont_param_hint = Exactly of Name.t * t
                             | Temp of t
                             | Anon  

    datatype cont = FnCont of cont_param_hint * (expr option -> expr)
                  | TrivCont of expr

    fun convertExpr cont =
        fn FAst.Term.Const (pos, c) => continue (Const (pos, c)) cont

    and continue expr =
        fn FnCont (_, k) => k (SOME expr)

    fun cpsConvert program =
        let val pos = FAst.Term.stmtPos (Vector.sub (program, 0))
        in convertExpr (TrivCont (raise Fail "unimplemented"))
                       (FAst.Term.Let ( pos
                                      , program
                                      , FAst.Term.Const (pos, Const.Int 0) ))
        end
end
