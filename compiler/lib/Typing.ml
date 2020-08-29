module Make (E : TyperSigs.ELABORATION) (M : TyperSigs.MATCHING) : TyperSigs.TYPING = struct

module AExpr = Ast.Term.Expr
module FExpr = Fc.Term.Expr
module AStmt = Ast.Term.Stmt
module FStmt = Fc.Term.Stmt
module T = Fc.Type
module Err = TypeError

type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a TyperSigs.typing

let const_typ c = T.Prim (match c with
    | Const.Int _ -> Prim.Int)

let rec typeof : Env.t -> AExpr.t with_pos -> FExpr.t with_pos typing
= fun env expr -> match expr.v with
    | AExpr.Values exprs ->
        if Vector.length exprs = 1
        then typeof env (Vector.get exprs 0)
        else failwith "TODO: typeof multi-Values"

    | AExpr.Fn clauses ->
        (match Vector.to_seq clauses () with
        | Cons (clause, clauses') ->
            let (env, universals) = Env.push_existential env in
            let (domain, {TyperSigs.term = clause; typ = codomain; eff}) =
                elaborate_clause env clause in
            let clauses' = Seq.map (check_clause env domain eff ((* HACK: *) T.to_abs codomain))
                clauses' in
            let clauses = Vector.of_seq (fun () -> Seq.Cons (clause, clauses')) in
            let params = clause . FExpr.pats in (* HACK *)
            let param_uses =
                Vector.map (fun {FExpr.name; _} -> {expr with v = FExpr.Use name}) params in
            let body = {expr with v = FExpr.Match (param_uses, clauses)} in
            let universals = Vector.of_list !universals in
            let (_, substitution) = Vector.fold_left (fun (i, substitution) (name, _) ->
                (i + 1, Name.Map.add name i substitution)
            ) (0, Name.Map.empty) universals in
            { term = {expr with v = Fn (universals, params, body)}
            ; typ = Pi ( Vector.map snd universals
                       , Vector.map (fun (locator, domain) ->
                           ( Environmentals.close_locator env substitution locator
                           , Environmentals.close env substitution domain ))
                           domain
                       , Environmentals.close env substitution eff
                       , Environmentals.close_abs env substitution (T.to_abs codomain) )
            ; eff }
        | Nil -> failwith "TODO: clauseless fn")

    | AExpr.Thunk stmts ->
        let body = AExpr.App ( {expr with v = AExpr.Var (Name.of_string "do")}
            , Vector.singleton {expr with v = AExpr.Record stmts} ) in
        let clause = { AExpr.iparams = Vector.empty (); eparams = Vector.empty ()
            ; body = {expr with v = body} } in
        typeof env {expr with v = AExpr.Fn (Vector.singleton clause)}

    | AExpr.App (callee, args) ->
        let check_args env eff domain args =
            Vector.map2 (fun (locator, domain) ({v = _; pos} as arg : AExpr.t with_pos) ->
                let {TyperSigs.term = arg; typ = _; eff = arg_eff} = check env locator domain arg in
                let _ = M.solving_unify pos env arg_eff eff in
                arg)
                domain args in

        let {TyperSigs.term = callee; typ = callee_typ; eff = callee_eff} = typeof env callee in
        (match M.focalize callee.pos env callee_typ (PiL (Vector.length args, Hole)) with
        | (Cf coerce, Pi (universals, domain, app_eff, codomain)) ->
            let (uvs, domain, app_eff, codomain) =
                Environmentals.instantiate_arrow env universals domain app_eff codomain in
            let _ = M.solving_unify expr.pos env app_eff callee_eff in
            let args = check_args env app_eff domain args in
            let Exists (existentials, codomain_locator, concr_codomain) = codomain in
            (* FIXME: Use `existentials` *)
            { term = {expr with v = App (coerce callee, Vector.map (fun uv -> T.Uv uv) uvs, args)}
            ; typ = concr_codomain
            ; eff = app_eff }
        | _ -> failwith "compiler bug: callee focalization returned non-function")

    | AExpr.AppSequence exprs -> (* TODO: in/pre/postfix parsing, special forms, macros *)
        let callee = Vector1.get exprs 0 in
        let args = Vector.sub (Vector1.to_vector exprs) 1 (Vector1.length exprs - 1) in
        typeof env {expr with v = AExpr.App (callee, args)}

    | AExpr.PrimApp (op, args) -> (* TODO: DRY: *)
        let check_args env eff domain args =
            Vector.map2 (fun (locator, domain) ({v = _; pos} as arg : AExpr.t with_pos) ->
                let {TyperSigs.term = arg; typ = _; eff = arg_eff} = check env locator domain arg in
                let _ = M.solving_unify pos env arg_eff eff in
                arg)
                domain args in

        let (universals, domain, app_eff, codomain) = Primop.typeof op in
        let (uvs, domain, app_eff, Exists (_, _, codomain)) =
            Environmentals.instantiate_arrow env universals domain app_eff (T.to_abs codomain) in
        let args = check_args env app_eff domain args in
        { term = {expr with v = PrimApp (op, Vector.map (fun uv -> T.Uv uv) uvs, args)}
        ; typ = codomain
        ; eff = app_eff }

    | AExpr.Ann (expr, typ) ->
        let typ = E.elaborate env typ in
        (* FIXME: Abstract type generation effect *)
        check_abs env typ expr

    | AExpr.Proxy typ ->
        let typ = E.elaborate env {v = typ; pos = expr.pos} in
        {term = {expr with v = Proxy typ}; typ = Type typ; eff = EmptyRow}

    | AExpr.Var name ->
        {term = {expr with v = Use name}; typ = Env.find env expr.pos name; eff = EmptyRow}

    | AExpr.Const c -> {term = {expr with v = Const c}; typ = const_typ c; eff = EmptyRow}

and elaborate_clause env {iparams; eparams; body} =
    let (iparams, edomain, env) = elaborate_pats env iparams in
    let (eparams, idomain, env) = elaborate_pats env eparams in
    let {TyperSigs.term = body; typ = codomain; eff} = typeof env body in
    ( Vector.append edomain idomain
    , {term = {FExpr.pats = Vector.append iparams eparams; body}; typ = codomain ; eff} )

and check_clause env domain eff codomain {iparams; eparams; body} =
    let (pats, body_env) = check_pats env domain (Vector.append iparams eparams) in
    let {TyperSigs.term = body; typ = _; eff = body_eff} = check_abs body_env codomain body in
    ignore (M.solving_unify body.pos env body_eff eff);
    {pats; body}

and check_abs : Env.t -> T.abs -> AExpr.t with_pos -> FExpr.t with_pos typing
= fun env (Exists (existentials, locator, body)) expr ->
    if Vector.length existentials = 0
    then check env locator body expr
    else failwith "TODO: check_abs with existentials"

and check : Env.t -> T.locator -> T.t -> AExpr.t with_pos -> FExpr.t with_pos typing
= fun env locator typ expr -> match (typ, expr.v) with
    | (T.Pi (universals, domain, eff, codomain), AExpr.Fn clauses) ->
        (match Vector1.of_vector clauses with
        | Some clauses ->
            let clauses = Vector1.map (check_clause env domain eff codomain) clauses in
            let params = (Vector1.get clauses 0) . FExpr.pats in (* HACK *)
            let param_uses =
                Vector.map (fun {FExpr.name; _} -> {expr with v = FExpr.Use name}) params in
            let body = {expr with v = FExpr.Match (param_uses, Vector1.to_vector clauses)} in
            { term = {expr with v = Fn ((* FIXME: *) Vector.empty (), params, body)}
            ; typ; eff }
        | None -> failwith "TODO: check clauseless fn")
    | (Record row, _) -> failwith "TODO: check Record"
    | _ ->
        let {TyperSigs.term = expr; typ = expr_typ; eff} = typeof env expr in
        let Cf coerce = M.solving_subtype expr.pos env expr_typ locator typ in
        {term = coerce expr; typ; eff}

and elaborate_pat : Env.t -> AExpr.pat with_pos -> FExpr.lvalue * T.locator * T.t * Env.t
= fun env pat -> match pat.v with
    | AExpr.Values pats ->
        if Vector.length pats = 1
        then elaborate_pat env (Vector.get pats 0)
        else failwith "TODO: multi-value elaborate_pat"

    | AExpr.Ann (pat, typ) ->
        let (_, locator, typ) = E.elaborate env typ |> Environmentals.reabstract env in
        let (pat, env) = check_pat env typ pat in
        (pat, locator, typ, env)

    | AExpr.Var name ->
        let typ = T.Uv (Env.uv env (Name.fresh ())) in
        ({name; typ}, Hole, typ, Env.push_val env  name typ)

    | AExpr.Fn _ | AExpr.Thunk _ -> raise (Err.TypeError (pat.pos, NonPattern pat.v))

and elaborate_pats env pats =
    let step (pats, typs, env) pat =
        let (pat, loc, typ, env) = elaborate_pat env pat in
        (pat :: pats, (loc, typ) :: typs, env) in
    let (pats, typs, env) = Vector.fold_left step ([], [], env) pats in
    (Vector.of_list (List.rev pats), Vector.of_list (List.rev typs), env)

and check_pat : Env.t -> T.t -> AExpr.pat with_pos -> FExpr.lvalue * Env.t
= fun env typ pat -> match pat.v with
    | AExpr.Values pats when Vector.length pats = 1 ->
        if Vector.length pats = 1
        then check_pat env typ (Vector.get pats 0)
        else failwith "TODO: multi-value check_pat"

    | AExpr.Ann (pat', typ') ->
        let (_, locator, typ') = E.elaborate env typ' |> Environmentals.reabstract env in
        let coercion = M.solving_subtype pat.pos env typ locator typ' in (* FIXME: use coercion *)
        check_pat env typ' pat'

    | AExpr.Var name -> ({name; typ}, Env.push_val env name typ)

    | AExpr.Fn _ | AExpr.Thunk _ -> raise (Err.TypeError (pat.pos, NonPattern pat.v))

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

