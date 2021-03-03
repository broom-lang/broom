open Asserts
module AExpr = Ast.Term.Expr
module AStmt = Ast.Term.Stmt

type 'a with_pos = 'a Util.with_pos

module Make (Kinding : TyperSigs.KINDING) = struct

let typeof _ (expr : AExpr.t with_pos) = todo (Some expr.pos)

let check_interactive_stmts _ stmts =
    let span =
        let (start, _) = AStmt.pos (Vector1.get stmts 0) in
        let (_, stop) = AStmt.pos (Vector1.get stmts (Vector1.length stmts - 1)) in
        (start, stop) in
    todo (Some span)

end

