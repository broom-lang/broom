module Make (E : TyperSigs.ELABORATION) (M : TyperSigs.MATCHING) : TyperSigs.TYPING = struct

module AExpr = Ast.Term.Expr
module FExpr = Fc.Term.Expr
module AStmt = Ast.Term.Stmt
module FStmt = Fc.Term.Stmt
module T = Fc.Type

type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a TyperSigs.typing

let const_typ c = T.Prim (match c with
    | Const.Int _ -> Prim.Int)

let rec typeof env (expr : AExpr.t with_pos) : FExpr.t with_pos typing = match expr.v with
    | AExpr.Fn clauses ->
        (match Vector.to_seq clauses () with
        | Cons (clause, clauses') ->
            let (universals, domain, {TyperSigs.term = clause; typ = codomain; eff}) =
                elaborate_clause env clause in
            let clauses' = Seq.map (check_clause env domain eff codomain) clauses' in
            let clauses = Vector.of_seq (fun () -> Seq.Cons (clause, clauses')) in
            let params = clause . FExpr.pats in (* HACK *)
            let param_uses =
                Vector.map (fun {FExpr.name; _} -> {expr with v = FExpr.Use name}) params in
            let body = {expr with v = FExpr.Match (param_uses, clauses)} in
            { term = {expr with v = Fn ((* FIXME: *) Vector.empty (), params, body)}
            ; typ = Pi (universals, domain, eff, T.to_abs codomain)
            ; eff }
        | Nil -> failwith "TODO: clauseless fn")

    | AExpr.Ann (expr, typ) ->
        let typ = E.elaborate env typ in
        (* FIXME: Abstract type generation effect: *)
        check env typ expr

    | AExpr.Proxy typ ->
        let typ = E.elaborate env {v = typ; pos = expr.pos} in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = Prim EmptyRow}

    | AExpr.Use name ->
        {term = {expr with v = Use name}; typ = Env.find name env; eff = Prim EmptyRow}

    | AExpr.Const c -> {term = {expr with v = Const c}; typ = const_typ c; eff = Prim EmptyRow}

and elaborate_clause env {pats; body} =
    let (existentials, pats, domain, body_env) = elaborate_pats env pats in
    let {TyperSigs.term = body; typ = codomain; eff} = typeof body_env body in
    (existentials, domain, {term = {FExpr.pats; body}; typ = codomain ; eff})

and check_clause env domain codomain eff {pats; body} =
    let (pats, body_env) = check_pats env domain pats in
    let {TyperSigs.term = body; typ = _; eff = body_eff} = typeof body_env body in
    ignore (M.solving_unify body.pos env body_eff eff);
    {pats; body}

and check env typ expr = failwith "TODO: check"

and elaborate_pat env (pat : AExpr.pat with_pos) = match pat.v with
    | AExpr.Values pats ->
        if Vector.length pats = 1
        then elaborate_pat env (Vector.get pats 0)
        else failwith "TODO: multi-value elaborate_pat"

    | AExpr.Ann (pat, typ) ->
        let Exists (_, _, typ) as abs = E.elaborate env typ in
        let (pat, env) = check_pat env typ pat in
        (pat, abs, env)

and elaborate_pats env pats =
    let step (existentials, pats, typs, env) pat =
        let (pat, Exists (existentials', loc, typ), env) = elaborate_pat env pat in
        (Vector.append existentials existentials', pat :: pats, (loc, typ) :: typs, env) in
    let (existentials, pats, typs, env) = Vector.fold_left step (Vector.empty (), [], [], env) pats in
    (existentials, Vector.of_list (List.rev pats), Vector.of_list (List.rev typs), env)

and check_pat env (typ : T.t) (pat : AExpr.pat with_pos) : FExpr.lvalue * Env.t = match pat.v with
    | AExpr.Use name -> ({name; typ}, Env.add name typ env)

and check_pats env domain pats =
    let step (pats, env) (_, domain) pat =
        let (pat, env) = check_pat env domain pat in
        (pat :: pats, env) in
    let (pats, env) = Vector.fold_left2 step ([], env) domain pats in
    (Vector.of_list (List.rev pats), env)

let deftype _ = failwith "TODO: deftype"

let check_stmt env : AStmt.t -> FStmt.t typing * Env.t = function
    | AStmt.Def (pos, pat, expr) ->
        let {term = expr; typ; eff} : FExpr.t with_pos typing = typeof env expr in
        let (pat, env) = check_pat env typ pat in
        ({term = FStmt.Def (pos, pat, expr); typ; eff}, env)

    | AStmt.Expr expr ->
        let typing = typeof env expr in
        ({typing with term = FStmt.Expr typing.term}, env)

let lookup _ = failwith "TODO: lookup"

end

