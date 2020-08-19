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
    | AExpr.Proxy typ ->
        let typ = E.elaborate env {v = typ; pos = expr.pos} in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = Prim EmptyRow}

    | AExpr.Use name ->
        {term = {expr with v = Use name}; typ = Env.find name env; eff = Prim EmptyRow}

    | AExpr.Const c -> {term = {expr with v = Const c}; typ = const_typ c; eff = Prim EmptyRow}

let check_pat env typ (pat : AExpr.pat with_pos) : FExpr.lvalue * Env.t = match pat.v with
    | AExpr.Use name -> ({name; typ}, Env.add name typ env)

let deftype _ = failwith "TODO"

let check_stmt env : AStmt.t -> FStmt.t typing * Env.t = function
    | AStmt.Def (pos, pat, expr) ->
        let {term = expr; typ; eff} : FExpr.t with_pos typing = typeof env expr in
        let (pat, env) = check_pat env typ pat in
        ({term = FStmt.Def (pos, pat, expr); typ; eff}, env)

    | AStmt.Expr expr ->
        let typing = typeof env expr in
        ({typing with term = FStmt.Expr typing.term}, env)

let lookup _ = failwith "TODO"

end

