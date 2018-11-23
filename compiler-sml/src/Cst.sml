structure Cst :> sig
    datatype expr = Fn of Pos.t * Name.t * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | Use of Pos.t * Name.t
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * Name.t * expr

    val stmtToString: stmt -> string
    val exprToString: expr -> string
end = struct
    datatype expr = Fn of Pos.t * Name.t * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | Use of Pos.t * Name.t
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * Name.t * expr

    val rec stmtToString = fn Def (_, name, valExpr) =>
                               "val " ^ Name.toString name ^ " = " ^ exprToString valExpr
    and exprToString = fn Fn (_, param, body) =>
                           "fn " ^ Name.toString param ^ " => " ^ exprToString body
                        | App (_, {callee, arg}) =>
                           "(" ^ exprToString callee ^ " " ^ exprToString arg ^ ")"
                        | Use (_, name) => Name.toString name
                        | Const (_, c) => Const.toString c
end