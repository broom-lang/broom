structure Typecheck :> sig
    val typecheck: Cst.stmt vector -> Cst.stmt vector
end = struct
    val constType = fn Const.Int _ => Type.Int

    fun check (Cst.Const (pos, c)) = (Cst.Const (pos, c), constType c)

    and checkStmt (Cst.Def (pos, name, expr)) =
        let val (expr', t) = check expr
        in (Cst.Def (pos, name, expr'), t)
        end

    fun typecheck program = Vector.map (#1 o checkStmt) program
end
