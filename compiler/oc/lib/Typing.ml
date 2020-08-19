module Make (E : TyperSigs.ELABORATION) (M : TyperSigs.MATCHING) : TyperSigs.TYPING = struct

module AExpr = Ast.Term.Expr
module FExpr = FcTerm.Expr
module AStmt = Ast.Term.Stmt
module FStmt = FcTerm.Stmt
module T = FcType

type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a TyperSigs.typing

let const_typ c = T.Prim (match c with
    | Const.Int _ -> Prim.Int)

let typeof env (expr : AExpr.t with_pos) : FExpr.t with_pos typing = match expr.v with
    | AExpr.Const c -> {term = {expr with v = Const c}; typ = const_typ c; eff = Prim EmptyRow}

let deftype _ = failwith "TODO"

let check_stmt env = function
    | AStmt.Expr expr ->
        let typing = typeof env expr in
        {typing with term = FStmt.Expr typing.term}

let lookup _ = failwith "TODO"

end

