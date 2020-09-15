module TS = TyperSigs

module Make
    (Env : TS.ENV)
    (K : TS.KINDING with type env = Env.t)
    (M : TS.MATCHING with type env = Env.t)
: TS.TYPING with type env = Env.t
= struct

module AExpr = Ast.Term.Expr
module FExpr = Fc.Term.Expr
module AStmt = Ast.Term.Stmt
module FStmt = Fc.Term.Stmt
module T = Fc.Type
module Err = TypeError

type env = Env.t
type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a TS.typing

let (!) = TxRef.(!)

(* # Synthesis *)

let const_typ c = T.Prim (match c with
    | Const.Int _ -> Prim.Int)

let primop_typ =
    let open Primop in
    function
    | IAdd | ISub | IMul ->
        ( Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
        , T.EmptyRow, T.Prim Prim.Int )
    | Int ->
        (Vector.empty, Vector.empty, T.EmptyRow, T.Proxy (T.to_abs (Prim Int)))
    | Type ->
        ( Vector.empty, Vector.empty, T.EmptyRow
        , T.Proxy (T.Exists (Vector.singleton T.aType
            , Proxy (T.to_abs (Bv {depth = 1; sibli = 0; kind = T.aType})))) )

let rec typeof : Env.t -> AExpr.t with_pos -> FExpr.t with_pos typing
= fun env expr -> match expr.v with
    | AExpr.Values exprs when Vector.length exprs = 1 -> typeof env (Vector.get exprs 0)

    | AExpr.Values exprs ->
        let exprs' = CCVector.create () in
        let typs = CCVector.create () in
        let eff : T.t = Uv (Env.uv env T.aRow (Name.fresh ())) in
        exprs |> Vector.iter (fun expr ->
            let {TS.term = expr; typ; eff = eff'} = typeof env expr in
            CCVector.push exprs' expr;
            CCVector.push typs typ;
            ignore (M.solving_unify expr.pos env eff' eff)
        );
        { term = {expr with v = Values (Vector.build exprs')}
        ; typ = Values (Vector.build typs)
        ; eff }

    | AExpr.Fn clauses -> elaborate_fn env expr.pos clauses

    | AExpr.Thunk stmts ->
        let body = AExpr.App ( {expr with v = AExpr.Var (Name.of_string "do")}
            , {expr with v = AExpr.Record stmts} ) in
        let {TS.term = body; typ = codomain; eff} = typeof env {expr with v = body} in
        { term = {expr with v = FExpr.Fn (Vector.empty, {name = Name.fresh (); typ = Values Vector.empty}, body)}
        ; typ = Pi {universals = Vector.empty; idomain = None
            ; edomain = Values Vector.empty; eff; codomain = T.to_abs codomain }
        ; eff = EmptyRow }

    | AExpr.App (callee, arg) ->
        let {TS.term = callee; typ = callee_typ; eff = callee_eff} = typeof env callee in
        (match M.focalize callee.pos env callee_typ (PiL Hole) with
        | (Cf coerce, Pi {universals; idomain; edomain; eff = app_eff; codomain}) ->
            let (uvs, idomain, edomain, app_eff, codomain) =
                Env.instantiate_arrow env universals idomain edomain app_eff codomain in
            let _ = M.solving_unify expr.pos env app_eff callee_eff in
            let {TS.term = arg; typ = _; eff = arg_eff} = check env edomain arg in
            let _ = M.solving_unify expr.pos env arg_eff callee_eff in
            let Exists (existentials, concr_codomain) = codomain in
            (* FIXME: Use `existentials` *)
            { term = {expr with v = App (coerce callee, Vector.map (fun uv -> T.Uv uv) uvs, arg)}
            ; typ = concr_codomain
            ; eff = app_eff }
        | _ -> failwith "compiler bug: callee focalization returned non-function")

    | AExpr.AppSequence exprs -> (* TODO: in/pre/postfix parsing, special forms, macros *)
        let callee = Vector1.get exprs 0 in
        let args = Vector.sub (Vector1.to_vector exprs) 1 (Vector1.length exprs - 1) in
        let arg = if Vector.length args = 1
            then Vector.get args 0
            else {expr with v = Values args} in
        typeof env {expr with v = AExpr.App (callee, arg)}

    | AExpr.PrimApp (op, arg) -> (* TODO: DRY: *)
        let (universals, domain, app_eff, codomain) = primop_typ op in
        let (uvs, idomain, domain, app_eff, Exists (_, codomain)) =
            Env.instantiate_arrow env universals None (Values domain) app_eff (T.to_abs codomain) in
        let {TS.term = arg; typ = _; eff = arg_eff} = check env domain arg in
        let _ = M.solving_unify arg.pos env arg_eff app_eff in
        { term = {expr with v = PrimApp (op, Vector.map (fun uv -> T.Uv uv) uvs, arg)}
        ; typ = codomain
        ; eff = app_eff }

    | AExpr.Record stmts -> typeof_record env expr.pos stmts

    | AExpr.Select (record, label) -> (* TODO: lacks-constraint: *)
        let field : T.t = Uv (Env.uv env T.aType (Name.fresh ())) in
        let typ : T.t = Record (With {base = Uv (Env.uv env T.aRow (Name.fresh ())); label; field}) in
        let {TS.term = record; typ = record_typ; eff} = check env typ record in
        {TS.term = {expr with v = Select (record, label)}; typ = field; eff}

    | AExpr.Ann (expr, typ) ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let typ = K.check env kind typ in
        (* FIXME: Abstract type generation effect *)
        check_abs env typ expr

    | AExpr.Proxy typ ->
        let {TS.typ; kind} = K.kindof env {v = typ; pos = expr.pos} in
        {term = {expr with v = Proxy typ}; typ = Proxy typ; eff = EmptyRow}

    | AExpr.Var name ->
        {term = {expr with v = Use name}; typ = Env.find env expr.pos name; eff = EmptyRow}

    | AExpr.Const c -> {term = {expr with v = Const c}; typ = const_typ c; eff = EmptyRow}

and elaborate_fn : Env.t -> Util.span -> AExpr.clause Vector.t -> FExpr.t with_pos typing
= fun env pos clauses -> match Vector.to_seq clauses () with
    | Cons (clause, clauses') ->
        let (env, universals) = Env.push_existential env in
        let (idomain, edomain, {TS.term = clause; typ = codomain; eff}) =
            elaborate_clause env clause in
        let clauses' = Seq.map (check_clause env idomain edomain eff ((* HACK: *) T.to_abs codomain))
            clauses' in
        let clauses = Vector.of_seq (fun () -> Seq.Cons (clause, clauses')) in
        let param = {FExpr.name = Name.fresh (); typ = edomain} in
        let param_use = {Util.v = FExpr.Use param.name; pos} in
        let body = {Util.v = FExpr.Match (param_use, clauses); pos} in
        let universals = Vector.map fst (Vector.of_list !universals) in
        let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
            (i + 1, Name.Map.add name i substitution)
        ) (0, Name.Map.empty) universals in
        { TS.term = {Util.v = FExpr.Fn (universals, param, body); pos}
        ; typ = Pi { universals = Vector.map snd universals
                   ; idomain = Option.map (Env.close env substitution) idomain
                   ; edomain = Env.close env substitution edomain
                   ; eff = Env.close env substitution eff
                   ; codomain = Env.close_abs env substitution (T.to_abs codomain) }
        ; eff = EmptyRow }
    | Nil -> failwith "TODO: clauseless fn"

and elaborate_clause env {iparam; eparam; body} =
    let (iparam, idomain, env) = match iparam with
        | Some iparam ->
            let (iparam, (_, idomain), idefs) = elaborate_pat env iparam in
            ( Some iparam, Some idomain
            , Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env idefs )
        | None -> (None, None, env) in
    let (eparam, (_, edomain), edefs) = elaborate_pat env eparam in
    let env = Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env edefs in
    let pat = match iparam with
        | Some iparam -> {iparam with Util.v = FExpr.ValuesP (Vector.of_list [iparam; eparam])}
        | None -> eparam in
    let {TS.term = body; typ = codomain; eff} = typeof env body in
    ( idomain, edomain
    , {term = {FExpr.pat; body}; typ = codomain ; eff} )

and elaborate_pats env pats =
    let step (pats, typs, defs, env) pat =
        let (pat, (_, typ), defs') = elaborate_pat env pat in
        let env =
            Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env defs' in
        (pat :: pats, typ :: typs, Vector.append defs defs', env) in
    let (pats, typs, defs, env) = Vector.fold step ([], [], Vector.empty, env) pats in
    (Vector.of_list (List.rev pats), Vector.of_list (List.rev typs), defs, env)

and elaborate_pat env pat = match pat.v with
    | AExpr.Values pats when Vector.length pats = 1 -> elaborate_pat env (Vector.get pats 0)

    | AExpr.Values pats ->
        let (pats, typs, defs, env) = elaborate_pats env pats in
        ({pat with v = FExpr.ValuesP pats}, (Vector.empty, Values typs), defs)

    | AExpr.Ann (pat, typ) ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let typ = K.check env kind typ in
        let (_, typ) as semiabs = Env.reabstract env typ in
        let (pat, defs) = check_pat env typ pat in
        (pat, semiabs, defs)

    | AExpr.Var name ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let typ = T.Uv (Env.uv env kind (Name.fresh ())) in
        ({pat with v = FExpr.UseP name}, (Vector.empty, typ), Vector.singleton {FExpr.name; typ})

    | AExpr.Proxy carrie ->
        let {TS.typ = carrie; kind} = K.kindof env {pat with v = carrie} in
        ({pat with v = ProxyP carrie}, (Vector.empty, Proxy carrie), Vector.empty)

    | AExpr.Const c ->
        ({pat with v = FExpr.ConstP c}, (Vector.empty, const_typ c), Vector.empty)

    | AExpr.AppSequence _ | AExpr.App _ | AExpr.PrimApp _ | AExpr.Select _ | AExpr.Record _ ->
        failwith "TODO in elaborate_pat"

    | AExpr.Fn _ | AExpr.Thunk _ -> raise (Err.TypeError (pat.pos, NonPattern pat.v))

(* TODO: Field punning (tricky because the naive translation `letrec x = x in {x = x}` makes no sense) *)
and typeof_record env pos stmts =
    let (pats, pat_typs, defs, env) = Vector.fold (fun (pats, semiabsen, defs, env) stmt ->
        let (pat, semiabs, defs') = analyze_field env stmt in
        let env = Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ)
            env defs' in
        (pat :: pats, semiabs :: semiabsen, Vector.append defs defs', env))
        ([], [], Vector.empty, env) stmts in
    let pats = Vector.of_list (List.rev pats) in
    let pat_typs = Vector.of_list (List.rev pat_typs) in

    let stmts = Vector.map3 (elaborate_field env) pats pat_typs stmts in

    let term = {Util.v = FExpr.Record (Vector.map (fun {FExpr.name; typ = _} ->
        (name, {Util.v = FExpr.Use name; pos})
    ) defs); pos} in
    let term = match Vector1.of_vector stmts with
        | Some stmts -> {Util.v = FExpr.Letrec (stmts, term); pos}
        | None -> term in
    let typ = Vector.fold (fun base {FExpr.name; typ} -> T.With {base; label = name; field = typ})
        T.EmptyRow defs
        |> (fun row -> T.Record row) in
    let eff = T.EmptyRow in
    {term; typ; eff}

and analyze_field env = function
    | AStmt.Def (_, pat, _) -> elaborate_pat env pat
    | AStmt.Expr {v = Var _; pos = _} -> failwith "TODO: field punning"
    | AStmt.Expr expr as field -> raise (Err.TypeError (expr.pos, Err.InvalidField field))

and elaborate_field env pat semiabs = function
    | AStmt.Def (pos, _, expr) ->
        let {TS.term = expr; typ = _; eff} = implement env semiabs expr in
        let _ = M.solving_unify expr.pos env eff EmptyRow in
        (pos, pat, expr)
    | AStmt.Expr {v = Var _; pos = _} -> failwith "TODO: field punning"
    | AStmt.Expr expr as field -> raise (Err.TypeError (expr.pos, Err.InvalidField field))

(* # Checking *)

and check_abs : Env.t -> T.abs -> AExpr.t with_pos -> FExpr.t with_pos typing
= fun env typ expr -> implement env (Env.reabstract env typ) expr

and implement : Env.t -> T.ov Vector.t * T.t -> AExpr.t with_pos -> FExpr.t with_pos typing
= fun env (existentials, typ) expr ->
    match Vector1.of_vector existentials with
    | Some existentials ->
        let axiom_bindings = Vector1.map (fun (((name, kind), _) as param) ->
            (Name.fresh (), param, Env.uv env kind name)
        ) existentials in
        let env = Env.push_axioms env axiom_bindings in
        let {TS.term; typ = _; eff} = check env typ expr in
        let axioms = Vector1.map (fun (axname, (((_, kind), _) as ov), impl) ->
            let rec to_axiom params acc i = function
                | T.Pi {universals = _; idomain = _; edomain = domain; eff = _
                    ; codomain = Exists (cd_existentials, codomain)} ->
                    CCVector.push params domain;
                    let acc = T.App (acc, (Bv {depth = 0; sibli = i; kind = domain})) in
                    to_axiom params acc (i + 1) codomain
                | _ -> (axname, Vector.build params, acc, T.Uv impl) in
            to_axiom (CCVector.create ()) (Ov ov) 0 kind
        ) axiom_bindings in
        {term = {expr with v = Axiom (axioms, term)}; typ; eff}
    | None -> check env typ expr

and check : Env.t -> T.t -> AExpr.t with_pos -> FExpr.t with_pos typing
= fun env typ expr -> match (typ, expr.v) with
    | (T.Values typs, AExpr.Values exprs) ->
        let exprs' = CCVector.create () in
        let typs' = CCVector.create () in
        let eff : T.t = Uv (Env.uv env T.aRow (Name.fresh ())) in
        (* FIXME: raises on length mismatch: *)
        Vector.iter2 (fun typ expr ->
            let {TS.term = expr; typ; eff = eff'} = check env typ expr in
            CCVector.push exprs' expr;
            CCVector.push typs' typ;
            ignore (M.solving_unify expr.pos env eff' eff)
        ) typs exprs;
        { term = {expr with v = Values (Vector.build exprs')}
        ; typ = Values (Vector.build typs')
        ; eff }

    | (Pi _, AExpr.Fn clauses) -> check_fn env typ expr.pos clauses

    | (Record row, AExpr.Record stmts) -> failwith "TODO: check Record"

    | _ ->
        let {TS.term = expr; typ = expr_typ; eff} = typeof env expr in
        let Cf coerce = M.solving_subtype expr.pos env expr_typ typ in
        {term = coerce expr; typ; eff}

and check_fn : Env.t -> T.t -> Util.span -> AExpr.clause Vector.t -> FExpr.t with_pos typing
= fun env typ pos clauses -> match typ with
    | T.Pi {universals; idomain; edomain; eff; codomain} ->
        (match Vector1.of_vector clauses with
        | Some clauses ->
            let clauses = Vector1.map (check_clause env idomain edomain eff codomain) clauses in
            let param = {FExpr.name = Name.fresh (); typ} in
            let param_use = {Util.v = FExpr.Use param.name; pos} in
            let body = {Util.v = FExpr.Match (param_use, Vector1.to_vector clauses); pos} in
            { term = {v = Fn ((* FIXME: *) Vector.empty, param, body); pos}
            ; typ; eff }
        | None -> failwith "TODO: check clauseless fn")
    | _ -> failwith "unreachable: non-Pi `typ` in `check_fn`"

and check_clause env idomain edomain eff codomain {iparam; eparam; body} =
    let (ipat, body_env) = match (idomain, iparam) with
        | (Some idomain, Some iparam) ->
            let (ipat, idefs) = check_pat env idomain iparam in
            (Some ipat, Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env idefs)
        | (None, None) -> (None, env) in
    let (epat, edefs) = check_pat env edomain eparam in
    let body_env = Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) body_env edefs in
    let pat = match ipat with
        | Some ipat -> {ipat with Util.v = FExpr.ValuesP (Vector.of_list [ipat; epat])}
        | None -> epat in
    let {TS.term = body; typ = _; eff = body_eff} = check_abs body_env codomain body in
    ignore (M.solving_unify body.pos env body_eff eff);
    {pat; body}

(* TODO: use coercions (and subtyping ?): *)
and check_pat : Env.t -> T.t -> AExpr.pat with_pos -> FExpr.pat with_pos * FExpr.lvalue Vector.t
= fun env typ pat -> match pat.v with
    | AExpr.Values pats when Vector.length pats = 1 -> check_pat env typ (Vector.get pats 0)

    | AExpr.Values pats -> failwith "TODO: multi-values in check_pat"

    | AExpr.Ann (pat', typ') ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let typ' = K.check env kind typ' in
        let (_, typ') = Env.reabstract env typ' in
        let _ = M.solving_unify pat.pos env typ typ' in
        check_pat env typ' pat'

    | AExpr.Var name -> ({pat with v = UseP name}, Vector.singleton {FExpr.name; typ})

    | AExpr.Proxy carrie ->
        let {TS.typ = carrie; kind} = K.kindof env {pat with v = carrie} in
        let _ = M.solving_unify pat.pos env typ (Proxy carrie) in
        ({pat with v = ProxyP carrie}, Vector.empty)

    | AExpr.Const c ->
        let _ = M.solving_unify pat.pos env typ (const_typ c) in
        ({pat with v = ConstP c}, Vector.empty)

    | AExpr.AppSequence _ | AExpr.App _ | AExpr.PrimApp _ | AExpr.Select _ | AExpr.Record _ ->
        failwith "TODO in check_pat"

    | AExpr.Fn _ | AExpr.Thunk _ -> raise (Err.TypeError (pat.pos, NonPattern pat.v))

and check_pats env domain pats =
    let step (pats, env) domain pat =
        let (pat, defs) = check_pat env domain pat in
        let env =
            Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env defs in
        (pat :: pats, env) in
    let (pats, env) = Vector.fold2 step ([], env) domain pats in (* FIXME: raises on length mismatch *)
    (Vector.of_list (List.rev pats), env)

(* # Statement Typing *)

let deftype _ = failwith "TODO: deftype"

let check_stmt : Env.t -> AStmt.t -> FStmt.t typing * Env.t
= fun env -> function
    | AStmt.Def (pos, pat, expr) ->
        let {term = expr; typ; eff} : FExpr.t with_pos typing = typeof env expr in
        let (pat, defs) = check_pat env typ pat in
        let env =
            Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env defs in
        ({term = FStmt.Def (pos, pat, expr); typ; eff}, env)

    | AStmt.Expr expr ->
        let typing = typeof env expr in
        ({typing with term = FStmt.Expr typing.term}, env)

(* # Lookup *)

let lookup _ = failwith "TODO: lookup"

end

