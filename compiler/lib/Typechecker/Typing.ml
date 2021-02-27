open Asserts
module AExpr = Ast.Term.Expr

type 'a with_pos = 'a Util.with_pos

module Make (Kinding : TyperSigs.KINDING) = struct
    let typeof _ (expr : AExpr.t with_pos) = todo (Some expr.pos)
end

