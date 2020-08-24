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

let rec typeof : Env.t -> AExpr.t with_pos -> FExpr.t with_pos typing
= fun env expr -> match expr.v with
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

    | AExpr.App (callee, args) ->
        let check_args env eff domain args =
            Vector.map2 (fun (_, domain) ({v = _; pos} as arg : AExpr.t with_pos) ->
                let {TyperSigs.term = arg; typ = _; eff = arg_eff} =
                    check env (T.to_abs domain) arg in
                let _ = M.solving_unify pos env arg_eff eff in
                arg)
                domain args in

        let {TyperSigs.term = callee; typ = callee_typ; eff = callee_eff} = typeof env callee in
        (match M.focalize callee.pos env callee_typ (PiL (Vector.length args, Hole)) with
        | (Cf coerce, Pi (universals, domain, app_eff, codomain)) ->
            (* FIXME: Universal instantiation *)
            let _ = M.solving_unify expr.pos env app_eff callee_eff in
            let args = check_args env app_eff domain args in
            let Exists (existentials, codomain_locator, concr_codomain) = codomain in
            (* FIXME: Use `existentials` *)
            { term = {expr with v = App (coerce callee, (* FIXME: *) Vector.empty (), args)}
            ; typ = concr_codomain
            ; eff = app_eff }
        | _ -> failwith "compiler bug: callee focalization returned non-function")

    | AppSequence exprs -> (* TODO: in/pre/postfix parsing, special forms, macros *)
        let callee = Vector1.get exprs 0 in
        let args = Vector.sub (Vector1.to_vector exprs) 1 (Vector1.length exprs - 1) in
        typeof env {expr with v = AExpr.App (callee, args)}

    | AExpr.Ann (expr, typ) ->
        let typ = E.elaborate env typ in
        (* FIXME: Abstract type generation effect: *)
        check env typ expr

    | AExpr.Proxy typ ->
        let typ = E.elaborate env {v = typ; pos = expr.pos} in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = Prim EmptyRow}

    | AExpr.Var name ->
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

and elaborate_pat : Env.t -> AExpr.pat with_pos -> FExpr.lvalue * T.abs * Env.t
= fun env pat -> match pat.v with
    | AExpr.Values pats ->
        if Vector.length pats = 1
        then elaborate_pat env (Vector.get pats 0)
        else failwith "TODO: multi-value elaborate_pat"

    | AExpr.Ann (pat, typ) ->
        let Exists (_, _, typ) as abs = E.elaborate env typ in
        let (pat, env) = check_pat env typ pat in
        (pat, abs, env)

    | AExpr.Var name ->
        let typ = T.Uv (Env.uv env (Name.fresh ())) in
        ({name; typ}, T.to_abs typ, Env.add name typ env)

and elaborate_pats env pats =
    let step (existentials, pats, typs, env) pat =
        let (pat, Exists (existentials', loc, typ), env) = elaborate_pat env pat in
        (Vector.append existentials existentials', pat :: pats, (loc, typ) :: typs, env) in
    let (existentials, pats, typs, env) = Vector.fold_left step (Vector.empty (), [], [], env) pats in
    (existentials, Vector.of_list (List.rev pats), Vector.of_list (List.rev typs), env)

and check_pat : Env.t -> T.t -> AExpr.pat with_pos -> FExpr.lvalue * Env.t
= fun env typ pat -> match pat.v with
    | AExpr.Var name -> ({name; typ}, Env.add name typ env)

and check_pats env domain pats =
    let step (pats, env) (_, domain) pat =
        let (pat, env) = check_pat env domain pat in
        (pat :: pats, env) in
    let (pats, env) = Vector.fold_left2 step ([], env) domain pats in (* FIXME: raises on length mismatch *)
    (Vector.of_list (List.rev pats), env)

let deftype _ = failwith "TODO: deftype"

let check_stmt : Env.t -> AStmt.t -> FStmt.t typing * Env.t
= fun env -> function
    | AStmt.Def (pos, pat, expr) ->
        let {term = expr; typ; eff} : FExpr.t with_pos typing = typeof env expr in
        let (pat, env) = check_pat env typ pat in
        ({term = FStmt.Def (pos, pat, expr); typ; eff}, env)

    | AStmt.Expr expr ->
        let typing = typeof env expr in
        ({typing with term = FStmt.Expr typing.term}, env)

let lookup _ = failwith "TODO: lookup"

end

