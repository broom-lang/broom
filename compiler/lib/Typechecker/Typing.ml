open Streaming
open Asserts

module TS = TyperSigs

module Make
    (Env : TS.ENV)
    (ExpandPats : TS.EXPAND_PATS with type env = Env.t)
    (K : TS.KINDING with type env = Env.t)
    (M : TS.MATCHING with type env = Env.t)
: TS.TYPING with type env = Env.t
= struct

module AExpr = Ast.Term.Expr
module FExpr = Fc.Term.Expr
type var = FExpr.var
module AStmt = Ast.Term.Stmt
module FStmt = Fc.Term.Stmt
module T = Fc.Type
module Err = TypeError

type env = Env.t
type 'a with_pos = 'a Util.with_pos
type 'a typing = 'a TS.typing

(* # Synthesis *)

let const_typ c = T.Prim (match c with
    | Const.Int _ -> Prim.Int
    | String _ -> String)

let primop_typ : Primop.t -> T.t Vector.t * T.t Vector.t * T.t * T.t =
    let open Primop in
    function
    | CellNew -> (* forall a . () -> __cell a *)
        ( Vector.singleton T.aType, Vector.empty
        , T.EmptyRow
        , T.App (Prim Cell, Bv {depth = 0; sibli = 0; kind = T.aType}) )
    | CellInit -> (* forall a . (__cell a, a) -> () *)
        ( Vector.singleton T.aType
        , Vector.of_list [ T.App (Prim Cell, Bv {depth = 0; sibli = 0; kind = T.aType})
            ; Bv {depth = 0; sibli = 0; kind = T.aType} ]
        , T.EmptyRow, T.Tuple Vector.empty )
    | CellGet -> (* forall a . __cell a -> a *)
        ( Vector.singleton T.aType
        , Vector.singleton (T.App (Prim Cell, Bv {depth = 0; sibli = 0; kind = T.aType}))
        , T.EmptyRow, T.Bv {depth = 0; sibli = 0; kind = T.aType} )
    | Int -> (Vector.empty, Vector.empty, T.EmptyRow, T.Proxy (Prim Int))
    | String -> (Vector.empty, Vector.empty, T.EmptyRow, T.Proxy (Prim String))
    | Type ->
        ( Vector.empty, Vector.empty, T.EmptyRow
        , T.Proxy (T.Exists (Vector1.singleton T.aType
            , Proxy (Bv {depth = 0; sibli = 0; kind = T.aType}))) )
    | TypeOf -> (* FIXME: Enforce argument purity *)
        ( Vector.singleton T.aType
        , Vector.singleton (T.Bv {depth = 0; sibli = 0; kind = T.aType})
        , EmptyRow, Proxy (Bv {depth = 0; sibli = 0; kind = T.aType}) )
    | Import ->
        ( Vector.singleton T.aType
        , Vector.of_list [T.Proxy (Bv {depth = 0; sibli = 0; kind = T.aType}); Prim String]
        , EmptyRow, Bv {depth = 0; sibli = 0; kind = T.aType} )
    | GlobalSet ->
        ( Vector.singleton T.aType
        , Vector.of_list [T.Prim String; Bv {depth = 0; sibli = 0; kind = T.aType}]
        , EmptyRow, Tuple Vector.empty )
    | GlobalGet ->
        ( Vector.singleton T.aType
        , Vector.singleton (T.Prim String)
        , EmptyRow, Bv {depth = 0; sibli = 0; kind = T.aType} )

let branchop_typ : Branchop.t -> T.t Vector.t * T.t Vector.t * T.t * T.t Vector.t =
    let open Branchop in
    function
    | IAdd | ISub | IMul | IDiv ->
        ( Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
        , T.EmptyRow, Vector.of_list [T.Prim Int; Tuple Vector.empty] )
    | ILt | ILe | IGt | IGe | IEq ->
        ( Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
        , T.EmptyRow, Vector.of_list [T.Tuple Vector.empty; Tuple Vector.empty] )

let rec typeof env expr : FExpr.t typing =
    check env (T.Uv (Env.uv env (T.App (Prim TypeIn, Uv (Env.uv env T.rep))))) expr

and emit_clause_body {FExpr.pat; body} =
    let pos = pat.ppos in
    fun ctx tmp_vars -> match ctx with
        | ExpandPats.Inline ->
            let defs = Stream.from (Vector.to_source tmp_vars)
                |> Stream.map (fun {ExpandPats.src_var; tmp_var} ->
                    FStmt.Def (pos, src_var, FExpr.at pos src_var.FExpr.vtyp (FExpr.use tmp_var)))
                |> Stream.into Sink.array in
            {body with term = FExpr.let' defs body}

        | Shared var ->
            let codomain = body.typ in
            if Vector.length tmp_vars = 1 then begin
                let {ExpandPats.tmp_var; src_var = _} = Vector.get tmp_vars 0 in
                let domain = tmp_var.vtyp in
                let ftyp = T.Pi { universals = Vector.empty; domain
                    ; eff = EmptyRow (* NOTE: effect does not matter any more... *)
                    ; codomain } in
                FExpr.at pos ftyp (FExpr.fn Vector.empty var body)
            end else begin
                let pos = body.pos in
                let domain : T.t = Tuple (Vector.map (fun (vars : ExpandPats.final_naming) ->
                    vars.src_var.vtyp
                ) tmp_vars) in
                let ftyp = T.Pi { universals = Vector.empty; domain
                    ; eff = EmptyRow (* NOTE: effect does not matter any more... *)
                    ; codomain } in
                let param = FExpr.fresh_var domain in
                let body = FExpr.at pos codomain (FExpr.let' (Stream.from (Vector.to_source tmp_vars)
                        |> Stream.indexed
                        |> Stream.map (fun (i, {ExpandPats.tmp_var = _; src_var}) ->
                            FStmt.Def (pos, src_var,
                                FExpr.at pos src_var.vtyp (FExpr.focus (FExpr.at pos domain (FExpr.use param)) i)))
                        |> Stream.into Sink.array)
                    body) in
                FExpr.at pos ftyp (FExpr.fn Vector.empty param body)
            end

        | Redirect dest ->
            let codomain = body.typ in
            if Vector.length tmp_vars = 1
            then begin
                let {ExpandPats.tmp_var; src_var = _} = Vector.get tmp_vars 0 in
                let domain = tmp_var.vtyp in
                let ftyp = T.Pi { universals = Vector.empty; domain
                    ; eff = EmptyRow (* NOTE: effect does not matter any more... *)
                    ; codomain } in
                FExpr.at pos codomain (FExpr.app (FExpr.at pos ftyp (FExpr.use dest)) Vector.empty
                    (FExpr.at pos domain (FExpr.use tmp_var)))
            end else begin
                let domain : T.t = Tuple (Vector.map (fun (vars : ExpandPats.final_naming) ->
                    vars.tmp_var.vtyp
                ) tmp_vars) in
                let ftyp = T.Pi { universals = Vector.empty; domain
                    ; eff = EmptyRow (* NOTE: effect does not matter any more... *)
                    ; codomain } in
                let args = Stream.from (Vector.to_source tmp_vars)
                    |> Stream.map (fun {ExpandPats.tmp_var; _} ->
                        FExpr.at pos tmp_var.vtyp (FExpr.use tmp_var))
                    |> Stream.into (Sink.buffer (Vector.length tmp_vars)) in
                FExpr.at pos codomain (FExpr.app (FExpr.at pos ftyp (FExpr.use dest)) Vector.empty
                    (FExpr.at pos domain (FExpr.values args)))
            end

and check_defs env defs =
    let pats = CCVector.create () in
    let bindings = CCVector.create () in
    let _ = Vector.fold (fun env def ->
        let (pat, semiabs, vars, expr) = analyze_def env def in
        CCVector.push pats pat;
        CCVector.push bindings (vars, semiabs, expr);
        Vector.fold (Env.push_val Explicit) env vars
    ) env defs in
    let pats = Vector.build pats in
    (* OPTIMIZE: Fields accumulator is not needed here, as `_` shows: *)
    (* FIXME: fields accumulator was used to put fields in dependency order! *)
    let (env, _) = Env.push_rec env (CCVector.freeze bindings) in

    ( Source.zip (Source.seq (CCVector.to_seq bindings))
            (Vector.to_source defs)
        |> Source.zip (Vector.to_source pats)
        |> Stream.from
        |> Stream.flat_map (elaborate_def env)
        |> Stream.into (Vector.sink ())
    , env )

and analyze_def env (_, pat, expr) =
    let (pat, semiabs, defs) = elaborate_pat env pat in
    (pat, semiabs, defs, expr)

and elaborate_def env (pat, ((vars, semiabs, _), (pos, _, expr))) : FStmt.def Stream.t =
    let {TS.term = expr; eff} =
        if Vector.length vars > 0
        then Env.find_rhs env pos (Vector.get vars 0).name
        else implement env semiabs expr in
    ignore (M.solving_unify expr.pos env eff EmptyRow);
    expand_def env vars pos pat expr

and expand_def env vars pos (pat : FExpr.pat) expr : FStmt.def Stream.t =
    if Vector.length vars = 1 then begin
        let var = Vector.get vars 0 in
        let typ = var.vtyp in
        let emit_final _ (tmp_vars : ExpandPats.final_naming Vector.t) =
            assert (Vector.length tmp_vars = 1);
            FExpr.at pat.ppos typ (FExpr.use (Vector.get tmp_vars 0).tmp_var) in
        let clauses = Vector.singleton {ExpandPats.pat; emit = emit_final} in
        let destructuring = ExpandPats.expand_clauses pat.ppos env typ expr clauses in
        Stream.single (pos, var, destructuring)
    end else begin
        let vars =
            let vars = Vector.to_array vars in
            Array.sort FExpr.Var.compare vars;
            Vector.of_array_unsafe vars in
        let typ : T.t = Tuple (Vector.map (fun (var : var) -> var.vtyp) vars) in
        let emit_final _ tmp_vars =
            FExpr.at pat.ppos typ (FExpr.values (Stream.from (Vector.to_source tmp_vars)
                |> Stream.map (fun {ExpandPats.tmp_var; _} ->
                    FExpr.at pat.ppos tmp_var.vtyp (FExpr.use tmp_var))
                |> Stream.into (Sink.buffer (Vector.length tmp_vars)))) in
        let clauses = Vector.singleton {ExpandPats.pat; emit = emit_final} in
        let destructuring = ExpandPats.expand_clauses pat.ppos env typ expr clauses in
        let tuple_var = FExpr.fresh_var typ in
        Stream.prepend (pos, tuple_var, destructuring)
            (Stream.from (Vector.to_source vars)
                |> Stream.indexed
                |> Stream.map (fun (index, (var : var)) ->
                    let focusee = FExpr.at pat.ppos tuple_var.vtyp (FExpr.use tuple_var) in
                    (pos, var, FExpr.at pat.ppos var.vtyp (FExpr.focus focusee index))))
    end

(* # Checking *)

and check_abs : Env.t -> T.t -> AExpr.t with_pos -> FExpr.t typing
= fun env typ expr -> implement env (Env.reabstract env typ) expr

and implement : Env.t -> T.ov Vector.t * T.t -> AExpr.t with_pos -> FExpr.t typing
= fun env (existentials, typ) expr ->
    if Vector.length existentials > 0 then begin
        let axiom_bindings = Vector.map (fun (((_, kind), _) as param) ->
            (Name.fresh (), param, Env.uv env kind)
        ) existentials in
        let env = Env.push_axioms env axiom_bindings in
        let {TS.term; eff} = check env typ expr in
        let axioms = Vector.map (fun (axname, (((_, kind), _) as ov), impl) ->
            let rec to_axiom params acc i = function
                | T.Pi {universals = _; domain; eff = _; codomain} ->
                    CCVector.push params domain;
                    let acc = T.App (acc, (Bv {depth = 0; sibli = i; kind = domain})) in
                    to_axiom params acc (i + 1) codomain
                | _ -> (axname, Vector.build params, acc, T.Uv impl) in
            to_axiom (CCVector.create ()) (Ov ov) 0 kind
        ) axiom_bindings in
        {term = FExpr.at expr.pos typ (FExpr.axiom axioms term); eff}
    end else check env typ expr

and check : Env.t -> T.t -> AExpr.t with_pos -> FExpr.t typing
= fun env typ expr ->
    let check_clause plicity env domain eff codomain ({params; body} : AExpr.clause) =
        let (pat, vars) = check_pat env domain params in
        let body_env = Vector.fold (Env.push_val plicity) env vars in
        let {TS.term = body; eff = body_eff} = check_abs body_env codomain body in
        ignore (M.solving_unify body.pos env body_eff eff);
        {FExpr.pat; body} in

    let rec check_whnf env typ expr =
        match typ with
        | T.Impli {universals; domain; codomain} -> (* OPTIMIZE: eta-expands: *)
            let (env, universals, domain, codomain) =
                Env.push_impli_skolems env universals domain codomain in
            let param = FExpr.fresh_var domain in
            let env = Env.push_val Implicit env param in
            let {TS.term = body; eff = body_eff} = check env codomain expr in
            ignore (M.solving_unify expr.pos env body_eff EmptyRow);
            let universals = Vector.map fst universals in
            { TS.term = FExpr.at expr.pos typ (FExpr.fn universals param body)
            ; eff = EmptyRow }

        | _ -> (match (typ, expr.v) with
            | (typ, Fn (Implicit, clauses)) ->
                let domain = T.Uv (Env.uv env (T.App (Prim TypeIn, Uv (Env.uv env T.rep)))) in
                let eff = T.EmptyRow in
                let codomain = T.Uv (Env.uv env (T.App (Prim TypeIn, Uv (Env.uv env T.rep)))) in
                let param = FExpr.fresh_var domain in
                let clauses = clauses |> Vector.map (fun clause ->
                    let clause = check_clause Implicit env domain eff codomain clause in
                    {ExpandPats.pat = clause.FExpr.pat; emit = emit_clause_body clause}
                ) in
                let matchee = FExpr.at expr.pos param.vtyp (FExpr.use param) in
                let body = ExpandPats.expand_clauses expr.pos env codomain matchee clauses in
                let universals = Vector.empty in (* FIXME *)
                let sub = T.Impli {universals; domain; codomain} in
                { term = FExpr.at expr.pos sub (FExpr.fn universals param body)
                    |> Coercer.apply_opt (M.solving_subtype expr.pos env sub typ)
                ; eff }

            | (typ, Fn (Explicit, clauses)) -> (* FIXME: special handling when `typ` is `... -> ...` *)
                let domain = T.Uv (Env.uv env (T.App (Prim TypeIn, Uv (Env.uv env T.rep)))) in
                let eff = T.Uv (Env.uv env T.aRow) in
                let codomain = T.Uv (Env.uv env (T.App (Prim TypeIn, Uv (Env.uv env T.rep)))) in
                let param = FExpr.fresh_var domain in
                let clauses = clauses |> Vector.map (fun clause ->
                    let clause = check_clause Explicit env domain eff codomain clause in
                    {ExpandPats.pat = clause.FExpr.pat; emit = emit_clause_body clause}
                ) in
                let matchee = FExpr.at expr.pos param.vtyp (FExpr.use param) in
                let body = ExpandPats.expand_clauses expr.pos env codomain matchee clauses in
                let universals = Vector.empty in (* FIXME *)
                let sub = T.Pi {universals; domain; eff; codomain} in
                { term = FExpr.at expr.pos sub (FExpr.fn universals param body)
                    |> Coercer.apply_opt (M.solving_subtype expr.pos env sub typ)
                ; eff }

            (* TODO: Effect opening à la Koka: *)
            | (codomain, App (callee, Explicit, arg)) -> (* OPTIMIZE: eta-expands universal callees: *)
                let {TS.term = arg; eff} = typeof env arg in
                let callee_typ = T.Pi {universals = Vector.empty
                    ; domain = arg.typ; eff; codomain} in
                let {TS.term = callee; eff = callee_eff} = check_whnf env callee_typ callee in
                ignore (M.solving_unify expr.pos env callee_eff eff);
                (match codomain with
                | Exists _ -> todo (Some expr.pos) ~msg: "existential codomain in App"
                | _ ->
                    { term = FExpr.at expr.pos codomain (FExpr.app callee Vector.empty arg)
                    ; eff })

            | (codomain, App (callee, Implicit, arg)) ->
                let {TS.term = arg; eff} = typeof env arg in
                let callee_typ = T.Impli {universals = Vector.empty
                    ; domain = arg.typ; codomain} in
                let {TS.term = callee; eff = callee_eff} = check_whnf env callee_typ callee in
                ignore (M.solving_unify expr.pos env callee_eff eff);
                { term = FExpr.at expr.pos codomain (FExpr.app callee Vector.empty arg)
                ; eff }

            | (_, PrimApp (_, Some _, _)) -> todo (Some expr.pos)

            | (codomain, PrimApp (op, None, arg)) ->
                let (universals, domain, app_eff, codomain') = primop_typ op in
                let (uvs, domain, app_eff, codomain') =
                    Env.instantiate_primop env universals domain app_eff codomain' in
                let domain = (* HACK *)
                    if Vector.length domain = 1
                    then Vector.get domain 0
                    else Tuple domain in
                (* TODO: Effect opening à la Koka: *)
                let {TS.term = arg; eff = arg_eff} = check env domain arg in
                ignore (M.solving_unify expr.pos env arg_eff app_eff);
                let universals = Vector.map (fun uv -> T.Uv uv) uvs in
                { term = FExpr.at expr.pos codomain' (FExpr.primapp op universals arg)
                    |> Coercer.apply_opt (M.solving_subtype expr.pos env codomain' codomain)
                ; eff = app_eff }

            | (_, PrimBranch (_, Some _, _, _)) -> todo (Some expr.pos)

            | (typ, PrimBranch (op, None, arg, clauses)) ->
                let (universals, domain, app_eff, codomain) = branchop_typ op in
                let (uvs, domain, app_eff, codomain) =
                    Env.instantiate_branch env universals domain app_eff codomain in
                (* TODO: Effect opening à la Koka: *)
                let {TS.term = arg; eff = arg_eff} = check_whnf env (Tuple domain) arg in
                ignore (M.solving_unify expr.pos env arg_eff app_eff);
                assert (Vector.length clauses = Vector.length codomain);
                let clauses = Stream.from (Source.zip (Vector.to_source codomain) (Vector.to_source clauses))
                    |> Stream.map (fun (codomain, {AExpr.params; body}) ->
                        let (pat, vars) = check_pat env codomain params in
                        let env = Vector.fold (Env.push_val Explicit) env vars in
                        let pat = match pat.pterm with
                            | VarP var -> Some var
                            | TupleP pats when Vector.length pats = 0 -> None
                            | _ -> failwith "complex PrimBranch pattern" in
                        let {TS.term = prim_body; eff = body_eff} = check_whnf env typ body in
                        ignore (M.solving_unify body.pos env body_eff app_eff);
                        {FExpr.res = pat; prim_body})
                    |> Stream.into (Vector.sink ()) in
                let universals = Vector.map (fun uv -> T.Uv uv) uvs in
                { term = FExpr.at expr.pos typ (FExpr.primbranch op universals arg clauses)
                ; eff = app_eff }

            | (typ, Let (defs, body)) ->
                let (defs, env) = check_defs env (Vector1.to_vector defs) in
                let {TS.term = body; eff} = check_whnf env typ body in
                {term = FExpr.at expr.pos typ (FExpr.letrec (Vector.to_array defs) body); eff}

            | (typ, Ann (expr, sub)) ->
                let sub = K.check env (App (Prim TypeIn, Uv (Env.uv env T.rep))) sub in
                let {TS.term; eff} = check_abs env sub expr in
                { term = term |> Coercer.apply_opt (M.solving_subtype expr.pos env sub typ)
                ; eff } (* FIXME: Abstract type generation effect *)

            | (Tuple typs, Tuple exprs) ->
                let exprs' = CCVector.create () in
                let typs' = CCVector.create () in
                let eff : T.t = Uv (Env.uv env T.aRow) in
                let typ_width = Vector.length typs in
                let expr_width = Vector.length exprs in
                if expr_width = typ_width then
                    Vector.iter2 (fun typ expr ->
                        let {TS.term = expr; eff = eff'} = check env typ expr in
                        CCVector.push exprs' expr;
                        CCVector.push typs' expr.typ;
                        ignore (M.solving_unify expr.pos env eff' eff)
                    ) typs exprs
                else
                    Env.reportError env expr.pos (TupleWidth (typ, typ_width, expr.v, expr_width));
                    { term = FExpr.at expr.pos (Tuple (Vector.build typs'))
                        (FExpr.values (CCVector.to_array exprs'))
                    ; eff }

            | (typ, Tuple exprs) ->
                let eff = T.Uv (Env.uv env T.aRow) in
                let exprs = exprs |> Vector.map (fun expr ->
                    let {TS.term; eff = eff'} = typeof env expr in
                    ignore (M.solving_unify expr.pos env eff' eff);
                    term) in
                let sub = T.Tuple (Vector.map (fun {FExpr.typ; _} -> typ) exprs) in
                { term = FExpr.at expr.pos sub (FExpr.values (Vector.to_array exprs))
                    |> Coercer.apply_opt (M.solving_subtype expr.pos env sub typ)
                ; eff }

            | (typ, Focus (tup, index)) ->
                (* TODO: get rid of focalization somehow (T.rep as a list instead of an array?) *)
                let {TS.term = tup; eff} = typeof env tup in
                (match M.focalize tup.pos env tup.typ (TupleL (index + 1)) with
                | (coerce_tup, Tuple typs) when index < Vector.length typs ->
                    let tup = Coercer.apply_opt coerce_tup tup in
                    let sub = Vector.get typs index in
                    { term = FExpr.at expr.pos sub (FExpr.focus tup index)
                        |> Coercer.apply_opt (M.solving_subtype expr.pos env sub typ)
                    ; eff }
                | _ -> bug (Some tup.pos) ~msg: "focusee focalization returned non-tuple")

            | (typ, Record stmts) ->
                (* TODO: Field punning (tricky because the naive translation `letrec x = x in {x = x}` makes no sense) *)
                let fields = CCVector.create () in
                let eff = T.Uv (Env.uv env T.aRow) in
                let sub = T.Record (Vector.fold (fun base -> function
                    | AStmt.Def (_, {v = Var label; _}, expr) ->
                        let {TS.term; eff = eff'} = typeof env expr in
                        CCVector.push fields (label, term);
                        ignore (M.solving_unify expr.pos env eff' eff);
                        T.With {base; label; field = term.typ}
                    | _ -> bug (Some expr.pos) ~msg: "bad record field reached typechecker"
                ) T.EmptyRow stmts) in
                { term = FExpr.at expr.pos sub (FExpr.record (CCVector.to_array fields))
                    |> Coercer.apply_opt (M.solving_subtype expr.pos env sub typ)
                ; eff }

            | (field, Select (selectee, label)) -> (* TODO: lacks-constraint: *)
                let base = T.Uv (Env.uv env T.aRow) in
                let selectee_typ = T.Record (With {base; label; field}) in
                let {TS.term = selectee; eff} = check_whnf env selectee_typ selectee in
                {TS.term = FExpr.at expr.pos typ (FExpr.select selectee label); eff}

            | (typ, Proxy carrie) -> (match typ with (* FIXME: uv *)
                | T.Proxy carrie' ->
                    let {TS.typ = carrie; kind = _} = K.kindof env {v = carrie; pos = expr.pos} in
                    ignore (M.solving_unify expr.pos env carrie carrie');
                    {term = FExpr.at expr.pos typ (FExpr.proxy carrie'); eff = EmptyRow}
                | _ -> todo (Some expr.pos) ~msg: "check proxy type error")

            | (typ, Const c) ->
                let sub = const_typ c in
                { term = FExpr.at expr.pos sub (FExpr.const c)
                    |> Coercer.apply_opt (M.solving_subtype expr.pos env sub typ)
                ; eff = EmptyRow }

            | (typ, Var name) ->
                let ({FExpr.vtyp = sub; _} as var, global) = Env.find env expr.pos name in
                let term =
                    if not global
                    then FExpr.use var
                    else
                        let namexpr = FExpr.at expr.pos (Prim String)
                            (FExpr.const (String (Name.to_string name))) in
                        FExpr.primapp GlobalGet (Vector.singleton typ)
                            (FExpr.at expr.pos (Tuple (Vector.singleton (T.Prim String)))
                                (FExpr.values [|namexpr|])) in
                { term = FExpr.at expr.pos sub term
                    |> Coercer.apply_opt (M.solving_subtype expr.pos env sub typ)
                ; eff = EmptyRow }

            | (_, Wild _) -> todo (Some expr.pos) ~msg: "elaborate _ expression"

            | (_, AppSequence _) ->
                bug (Some expr.pos) ~msg: "typechecker encountered AppSequence expression") in

    match K.eval expr.pos env typ with
    | Some (typ, None) -> check_whnf env typ expr
    | _ -> todo (Some expr.pos)

(* # Patterns *)

(* ## Synthesis *)

and elaborate_pat env pat : FExpr.pat * (T.ov Vector.t * T.t) * FExpr.var Vector.t =
    let elaborate_pats env pats =
        let step (env, pats, typs, defs) pat =
            let (pat, (_, typ), defs') = elaborate_pat env pat in
            let env = Vector.fold (Env.push_val Explicit) env defs' in
            (env, pat :: pats, typ :: typs, Vector.append defs defs') in
        let (_, pats, typs, defs) = Vector.fold step (env, [], [], Vector.empty) pats in
        (Vector.of_list (List.rev pats), Vector.of_list (List.rev typs), defs) in

    match pat.v with
    | AExpr.Tuple pats when Vector.length pats = 1 -> elaborate_pat env (Vector.get pats 0)

    | AExpr.Tuple pats ->
        let (pats, typs, defs) = elaborate_pats env pats in
        let ptyp : T.t = Tuple typs in
        ({ppos = pat.pos; pterm = FExpr.TupleP pats; ptyp}, (Vector.empty, ptyp), defs)

    | AExpr.Ann (pat, typ) ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
        let typ = K.check env kind typ in
        let (_, typ) as semiabs = Env.reabstract env typ in
        let (pat, defs) = check_pat env typ pat in
        (pat, semiabs, defs)

    | AExpr.Var name ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
        let ptyp = T.Uv (Env.uv env kind) in
        let var = FExpr.var name ptyp in
        ({ppos = pat.pos; pterm = VarP var; ptyp}, (Vector.empty, ptyp), Vector.singleton var)

    | AExpr.Wild name ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
        let ptyp = T.Uv (Env.uv env kind) in
        ({ppos = pat.pos; pterm = WildP name; ptyp}, (Vector.empty, ptyp), Vector.empty)

    | AExpr.Proxy carrie ->
        let {TS.typ = carrie; kind = _} = K.kindof env {pat with v = carrie} in
        let ptyp : T.t = Proxy carrie in
        ({ppos = pat.pos; pterm = ProxyP carrie; ptyp}, (Vector.empty, ptyp), Vector.empty)

    | AExpr.Const c ->
        let ptyp = const_typ c in
        ({ppos = pat.pos; pterm = ConstP c; ptyp}, (Vector.empty, ptyp), Vector.empty)

    | AExpr.Focus _ | Let _ | App _ | PrimApp _ | PrimBranch _ | Select _ | Record _ ->
        todo (Some pat.pos) ~msg: "in elaborate_pat"

    | AExpr.Fn _ ->
        Env.reportError env pat.pos (NonPattern pat.v);
        (* TODO: Treat as `_` instead: *)
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
        let ptyp = T.Uv (Env.uv env kind) in
        let var = FExpr.fresh_var ptyp in
        ( {ppos = pat.pos; pterm = VarP var; ptyp}, (Vector.empty, ptyp)
        , Vector.singleton var )

    | AppSequence _ -> bug (Some pat.pos) ~msg: "typechecker encountered AppSequence pattern"

(* ## Checking *)

(* TODO: use coercions (and subtyping ?): *)
and check_pat : Env.t -> T.t -> AExpr.pat with_pos -> FExpr.pat * FExpr.var Vector.t
= fun env ptyp pat ->
    let check_pats env domain pats =
        let step (env, pats, defs) domain pat =
            let (pat, defs') = check_pat env domain pat in
            (Vector.fold (Env.push_val Explicit) env defs, pat :: pats, Vector.append defs defs') in
        if Vector.length domain = Vector.length pats then begin
            let (_, pats, defs) = Vector.fold2 step (env, [], Vector.empty) domain pats in
            (Vector.of_list (List.rev pats), defs)
        end else failwith "tuple type and pattern widths don't match" in

    match pat.v with
    | AExpr.Tuple pats when Vector.length pats = 1 -> check_pat env ptyp (Vector.get pats 0)

    | AExpr.Tuple pats ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
        let typs = Vector.map (fun _ -> T.Uv (Env.uv env kind)) pats in
        let _ = M.solving_unify pat.pos env ptyp (Tuple typs) in
        let (pats, defs) = check_pats env typs pats in
        ({ppos = pat.pos; pterm = FExpr.TupleP pats; ptyp}, defs)

    | AExpr.Ann (pat', typ') ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
        let typ' = K.check env kind typ' in
        let (_, typ') = Env.reabstract env typ' in
        let _ = M.solving_unify pat.pos env ptyp typ' in
        check_pat env typ' pat'

    | AExpr.Var name ->
        let var = FExpr.var name ptyp in
        ({ppos = pat.pos; pterm = VarP var; ptyp}, Vector.singleton var)

    | AExpr.Wild name -> ({ppos = pat.pos; pterm = WildP name; ptyp}, Vector.empty)

    | AExpr.Proxy carrie ->
        let {TS.typ = carrie; kind = _} = K.kindof env {pat with v = carrie} in
        let _ = M.solving_unify pat.pos env ptyp (Proxy carrie) in
        ({ppos = pat.pos; pterm = ProxyP carrie; ptyp}, Vector.empty)

    | AExpr.Const c ->
        let _ = M.solving_unify pat.pos env ptyp (const_typ c) in
        ({ppos = pat.pos; pterm = ConstP c; ptyp}, Vector.empty)

    | AExpr.Focus _ | Let _ | App _ | PrimApp _ | PrimBranch _ | Select _ | Record _ ->
        todo (Some pat.pos) ~msg: "in check_pat"

    | AExpr.Fn _ ->
        Env.reportError env pat.pos (NonPattern pat.v);
        ({ppos = pat.pos; pterm = WildP (Name.of_string ""); ptyp}, Vector.empty)

    | AppSequence _ -> bug (Some pat.pos) ~msg: "typechecker encountered AppSequence pattern"

(* # Statement Typing *)

let check_stmt : Env.t -> AStmt.t -> FStmt.t Vector.t typing * T.t * Env.t
= fun env -> function
    | AStmt.Def (pos, pat, expr) ->
        let {term = expr; eff} : FExpr.t typing = typeof env expr in
        let (pat, vars) = check_pat env expr.typ pat in
        let defs = expand_def env vars pos pat expr
            |> Stream.map (fun def -> FStmt.Def def)
            |> Stream.into (Vector.sink ()) in
        ({term = defs; eff}, expr.typ, Vector.fold (Env.push_val Explicit) env vars)

    | AStmt.Expr expr ->
        let typing = typeof env expr in
        ({typing with term = Vector.singleton (FStmt.Expr typing.term)}, typing.term.typ, env)

let check_interactive_stmt env = function
    | AStmt.Def (pos, pat, expr) ->
        let {TS.term = expr; eff} = typeof env expr in
        let (pat, vars) = check_pat env expr.typ pat in
        let stmts = expand_def env vars pos pat expr
            |> Stream.flat_map (fun (((pos, var, _) as def) : FExpr.def) ->
                let typ = var.vtyp in
                let namexpr = FExpr.at pos (Prim String)
                    (FExpr.const (String (Name.to_string var.name))) in
                Stream.double
                    (FStmt.Def def)
                    (Expr (FExpr.at pos (Tuple Vector.empty)
                        (FExpr.primapp GlobalSet (Vector.singleton typ)
                            (FExpr.at pos (Tuple Vector.empty)
                            (FExpr.values [|namexpr; FExpr.at pos typ (FExpr.use var)|]))))))
            |> Stream.into Sink.array in
        (stmts, eff, Vector.fold (Env.push_val Explicit) env vars)
    | Expr expr ->
        let {TS.term = expr; eff} = typeof env expr in
        ([|FStmt.Expr expr|], eff, env)

let check_interactive_stmts env stmts =
    let pos =
        let (start, _) = AStmt.pos (Vector1.get stmts 0) in
        let (_, stop) = AStmt.pos (Vector1.get stmts (Vector1.length stmts - 1)) in
        (start, stop) in
    let stmts' = CCVector.create () in
    let eff = T.Uv (Env.uv env T.aRow) in
    let env = Vector1.fold (fun env stmt ->
        let (stmts'', stmt_eff, env) = check_interactive_stmt env stmt in
        ignore (M.solving_unify pos env stmt_eff eff);
        Array.iter (CCVector.push stmts') stmts'';
        env
    ) env stmts in
    let stmts = CCVector.to_array stmts' in
    let main =
        let (stmts, body) =
            if Array.length stmts > 0
            then match Array.get stmts 0 with
                | Expr expr -> (Array.sub stmts 0 (Array.length stmts - 1), expr)
                | _ -> (stmts, FExpr.at pos (Tuple Vector.empty) (FExpr.values [||]))
            else (stmts, FExpr.at pos (Tuple Vector.empty) (FExpr.values [||])) in
        FExpr.at pos body.typ (FExpr.let' stmts body) in
    ( { TS.term = { Fc.Program.type_fns = Env.type_fns env (* FIXME: gets all typedefs ever seen *)
                   ; defs = Vector.empty; main }
      ; eff }
    , env )

end

