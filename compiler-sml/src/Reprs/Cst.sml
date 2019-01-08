structure Cst :> sig
    datatype expr = Fn of Pos.t * Name.t * Type.t option * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | Let of Pos.t * stmt vector * expr
                  | Ann of Pos.t * expr * Type.t
                  | Use of Pos.t * Name.t
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * Name.t * Type.t option * expr

    val stmtToString: stmt -> string
    val exprToString: expr -> string
end = struct
    datatype expr = Fn of Pos.t * Name.t * Type.t option * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | Let of Pos.t * stmt vector * expr
                  | Ann of Pos.t * expr * Type.t
                  | Use of Pos.t * Name.t
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * Name.t * Type.t option * expr

    val rec stmtToString = fn Def (_, name, maybeAnn, valExpr) =>
                               "val " ^ Name.toString name ^
                                   (case maybeAnn
                                    of SOME ann => ": " ^ Type.toString ann
                                     | NONE => "") ^
                                   " = " ^ exprToString valExpr
    and exprToString = fn Fn (_, param, maybeAnn, body) =>
                           "fn " ^ Name.toString param ^
                               (case maybeAnn
                                of SOME t => ": " ^ Type.toString t
                                 | NONE => "") ^
                               " => " ^ exprToString body
                        | App (_, {callee, arg}) =>
                           "(" ^ exprToString callee ^ " " ^ exprToString arg ^ ")"
                        | Let (_, stmts, body) =>
                           let fun step (stmt, acc) = acc ^ stmtToString stmt ^
                           "\n"
                           in "let " ^ Vector.foldl step "" stmts ^ "in\n" ^
                                  "    " ^ exprToString body ^ "\nend"
                           end
                        | Ann (_, expr, t) => exprToString expr ^ ": " ^ Type.toString t
                        | Use (_, name) => Name.toString name
                        | Const (_, c) => Const.toString c
end
