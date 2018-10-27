structure Cst :> sig
    datatype expr = Const of Pos.t * Const.t
    and stmt = Def of Pos.t * Name.t * expr

    val stmtToString: stmt -> string
    val exprToString: expr -> string
end = struct
    datatype expr = Const of Pos.t * Const.t
    and stmt = Def of Pos.t * Name.t * expr

    val rec stmtToString = fn Def (_, name, valExpr) =>
                               "val " ^ Name.toString name ^ " = " ^ exprToString valExpr
    and exprToString = fn Const (_, c) => Const.toString c
end