open Streaming

module TS = TyperSigs

module Make
    (Env : TS.ENV)
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

let (!) = TxRef.(!)

(* # Synthesis *)

let const_typ c = T.Prim (match c with
    | Const.Int _ -> Prim.Int)

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
    | Int ->
        (Vector.empty, Vector.empty, T.EmptyRow, T.Proxy (Prim Int))
    | Type ->
        ( Vector.empty, Vector.empty, T.EmptyRow
        , T.Proxy (T.Exists (Vector1.singleton T.aType
            , Proxy (Bv {depth = 0; sibli = 0; kind = T.aType}))) )

let branchop_typ : Branchop.t -> T.t Vector.t * T.t Vector.t * T.t * T.t Vector.t =
    let open Branchop in
    function
    | IAdd | ISub | IMul | IDiv ->
        ( Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
        , T.EmptyRow, Vector.of_list [T.Prim Int; Tuple Vector.empty] )
    | ILt | ILe | IGt | IGe | IEq ->
        ( Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
        , T.EmptyRow, Vector.of_list [T.Tuple Vector.empty; Tuple Vector.empty] )

let rec typeof : Env.t -> AExpr.t with_pos -> FExpr.t typing
= fun env expr -> match expr.v with
    | AExpr.Tuple exprs when Vector.length exprs = 1 -> typeof env (Vector.get exprs 0)

    | AExpr.Tuple exprs ->
        let exprs' = CCVector.create () in
        let typs = CCVector.create () in
        let eff : T.t = Uv (Env.uv env T.aRow) in
        exprs |> Vector.iter (fun expr ->
            let {TS.term = expr; eff = eff'} = typeof env expr in
            CCVector.push exprs' expr;
            CCVector.push typs expr.typ;
            ignore (M.solving_unify expr.pos env eff' eff)
        ); 
        { term = FExpr.at expr.pos (T.Tuple (Vector.build typs))
            (FExpr.values (CCVector.to_array exprs'))
        ; eff }

    | AExpr.Focus (tup, index) ->
        let {TS.term = tup; eff} = typeof env tup in
        (match M.focalize tup.pos env tup.typ (TupleL (index + 1)) with
        | (Cf coerce, Tuple typs) when index < Vector.length typs ->
            (* FIXME: coercing potentially nontrivial expr `tup`: *)
            { term = FExpr.at expr.pos (Vector.get typs index) (FExpr.focus (coerce tup) index)
            ; eff }
        | _ -> failwith "compiler bug: focusee focalization returned non-tuple")

    | AExpr.Fn clauses -> elaborate_fn env expr.pos clauses

    | AExpr.App (callee, args) ->
        let {TS.term = callee; eff = callee_eff} = typeof env callee in
        (match M.focalize callee.pos env callee.typ (PiL Hole) with
        | (Cf coerce, Pi {universals; domain; codomain}) ->
            let (uvs, domain, codomain) = Env.instantiate_arrow env universals domain codomain in
            let arg = check_args env expr.pos domain callee_eff args in
            (match codomain with
            | Exists _ -> failwith "TODO: existential codomain in App"
            | _ ->
                { term = FExpr.at expr.pos codomain
                    (FExpr.app (coerce callee) (Vector.map (fun uv -> T.Uv uv) uvs) arg)
                ; eff = callee_eff })
        | _ -> failwith "compiler bug: callee focalization returned non-function")

    | AExpr.PrimApp (op, args) ->
        let (universals, domain, app_eff, codomain) = primop_typ op in
        let (uvs, domain, app_eff, codomain) =
            Env.instantiate_primop env universals domain app_eff codomain in
        let arg = check_args env expr.pos (Right {edomain = Tuple domain; eff = app_eff}) app_eff args in
        { term = FExpr.at expr.pos codomain (FExpr.primapp op (Vector.map (fun uv -> T.Uv uv) uvs) arg)
        ; eff = app_eff }

    | AExpr.PrimBranch (op, args, clauses) ->
        let (universals, domain, app_eff, codomain) = branchop_typ op in
        let (uvs, domain, app_eff, codomain) =
            Env.instantiate_branch env universals domain app_eff codomain in
        let arg = check_args env expr.pos (Right {edomain = Tuple domain; eff = app_eff}) app_eff args in
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
        let typ = T.Uv (Env.uv env kind) in
        assert (Vector.length clauses = Vector.length codomain);
        let clauses = Stream.from (Source.zip (Vector.to_source codomain) (Vector.to_source clauses))
            |> Stream.map (fun (codomain, {AExpr.params; body}) ->
                match params with
                | Right pat ->
                    let (pat, vars) = check_pat env codomain pat in
                    let env = Vector.fold Env.push_val env vars in
                    let pat = match pat.pterm with
                        | VarP var -> Some var
                        | TupleP pats when Vector.length pats = 0 -> None in
                    let {TS.term = prim_body; eff = body_eff} = check env typ body in
                    ignore (M.solving_unify body.pos env body_eff app_eff);
                    {FExpr.res = pat; prim_body})
            |> Stream.into (Vector.sink ()) in
        { term = FExpr.at expr.pos typ
            (FExpr.primbranch op (Vector.map (fun uv -> T.Uv uv) uvs) arg clauses)
        ; eff = app_eff }

    | AExpr.Let (defs, body) ->
        let (defs, env) = check_defs env (Vector1.to_vector defs) in
        let {TS.term = body; eff} = typeof env body in
        {term = FExpr.at expr.pos body.typ (FExpr.letrec (Vector.to_array defs) body); eff}

    | AExpr.Record stmts -> typeof_record env expr.pos stmts

    | AExpr.Select (selectee, label) -> (* TODO: lacks-constraint: *)
        let field : T.t = Uv (Env.uv env T.aType) in
        let typ : T.t = Record (With {base = Uv (Env.uv env T.aRow); label; field}) in
        let {TS.term = selectee; eff} = check env typ selectee in
        {TS.term = FExpr.at expr.pos field (FExpr.select selectee label); eff}

    | AExpr.Ann (expr, typ) ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
        let typ = K.check env kind typ in
        (* FIXME: Abstract type generation effect *)
        check_abs env typ expr

    | AExpr.Proxy typ ->
        let {TS.typ; kind = _} = K.kindof env {v = typ; pos = expr.pos} in
        {term = FExpr.at expr.pos (Proxy typ) (FExpr.proxy typ); eff = EmptyRow}

    | AExpr.Var name ->
        let {FExpr.vtyp = typ; _} as var = Env.find env expr.pos name in
        { term = FExpr.at expr.pos typ (FExpr.use var)
        ; eff = EmptyRow }

    | AExpr.Wild _ -> failwith "TODO: elaborate _ expression"

    | AExpr.Const c ->
        {term = FExpr.at expr.pos (const_typ c) (FExpr.const c); eff = EmptyRow}

    | AppSequence exprs ->
        failwith "compiler bug: typechecker encountered AppSequence expression"

and elaborate_fn : Env.t -> Util.span -> AExpr.clause Vector.t -> FExpr.t typing
= fun env pos clauses -> match Vector.to_seq clauses () with
    | Cons (clause, clauses') ->
        let (env, universals) = Env.push_existential env in
        let (domain, {TS.term = clause; eff = _}) = elaborate_clause env clause in
        let codomain = clause.FExpr.body.typ in
        let clauses' = Seq.map (check_clause env domain codomain) clauses' in
        let clauses = Vector.of_seq (fun () -> Seq.Cons (clause, clauses')) in
        let clauses = clauses |> Vector.map (fun ({FExpr.pat; body = _} as clause) ->
            {ExpandPats.pat; emit = emit_clause_body clause}
        ) in
        let domain_t : T.t = match domain with
            | Ior.Left idomain -> idomain
            | Right {T.edomain; eff = _} -> edomain
            | Both (idomain, {edomain; eff = _}) ->
                Tuple (Vector.of_list [idomain; edomain]) in
        let param = FExpr.fresh_var domain_t in
        let matchee = FExpr.at pos param.vtyp (FExpr.use param) in
        let body = ExpandPats.expand_clauses pos codomain matchee clauses in
        let universals = Vector.map fst (Vector.of_list !universals) in
        let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
            (i + 1, Name.Map.add name i substitution)
        ) (0, Name.Map.empty) universals in
        { TS.term = FExpr.at pos 
            (Pi { universals = Vector.map snd universals
                 ; domain = Ior.bimap (Env.close env substitution)
                      (fun {T.edomain; eff} ->
                          { T.edomain = Env.close env substitution edomain
                          ; eff = Env.close env substitution eff })
                      domain
                 ; codomain = Env.close env substitution codomain })
            (FExpr.fn universals param body)
        ; eff = EmptyRow }
    | Nil -> failwith "TODO: clauseless fn"

and elaborate_clause env {params; body} =
    let (pat, domain, eff, env) = match params with
        | Left ipat ->
            let (param, domain, env) = elaborate_param env ipat in
            (param, Ior.Left domain, T.EmptyRow, env)
        | Right epat ->
            let (param, domain, env) = elaborate_param env epat in
            (param, Right domain, T.Uv (Env.uv env T.aRow), env)
        | Both (ipat, epat) ->
            let (iparam, idomain, env) = elaborate_param env ipat in
            let (eparam, edomain, env) = elaborate_param env epat in
            ( { FExpr.ppos = iparam.ppos; pterm = FExpr.TupleP (Vector.of_list [iparam; eparam])
                ; ptyp = Tuple (Vector.of_list [iparam.ptyp; eparam.ptyp]) }
            , Both (idomain, edomain), T.Uv (Env.uv env T.aRow), env ) in
    let {TS.term = body; eff = body_eff} = typeof env body in
    ignore (M.solving_unify body.pos env eff body_eff);
    let domain = match domain with
        | Left idomain ->
            ignore (M.solving_unify body.pos env eff EmptyRow);
            Ior.Left idomain
        | Right edomain -> Right {T.edomain; eff}
        | Both (idomain, edomain) -> Both (idomain, {T.edomain; eff}) in
    (domain, {term = {FExpr.pat; body}; eff})

and check_args env pos domain eff args =
    let check_arg env pos domain eff arg =
        let {TS.term = arg; eff = arg_eff} = check env domain arg in
        let _ = M.solving_unify pos env arg_eff eff in
        arg in

    match domain with
    | Ior.Left idomain -> (match args with
        | Left arg ->
            (* TODO: Effect opening à la Koka: *)
            let _ = M.solving_unify pos env EmptyRow eff in
            check_arg env pos idomain eff arg
        | _ -> failwith "explicit arg passed to purely implicit callee")
    | Right {T.edomain; eff = app_eff} -> (match args with
        | Ior.Right arg ->
            (* TODO: Effect opening à la Koka: *)
            let _ = M.solving_unify pos env app_eff eff in
            check_arg env pos edomain eff arg
        | _ -> failwith "implicit arg passed to purely explicit callee")
    | Both (idomain, {edomain; eff = app_eff}) -> (match args with
        | Both (iarg, earg) ->
            (* TODO: Effect opening à la Koka: *)
            let _ = M.solving_unify pos env app_eff eff in
            let iarg = check_arg env pos idomain eff iarg in
            let earg = check_arg env pos edomain eff earg in
            FExpr.at iarg.pos (Tuple (Vector.of_list [iarg.typ; earg.typ]))
                (FExpr.values (Array.of_list [iarg; earg]))
        | Right _ -> failwith "TODO: Both App args"
        | Left _ -> failwith "missing explicit arg")

and emit_clause_body {FExpr.pat; body} =
    let pos = pat.ppos in
    fun ctx tmp_vars -> match ctx with
        | Inline ->
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
                let ftyp = T.Pi { universals = Vector.empty
                    ; domain = Ior.Right { edomain = domain 
                        ; eff = EmptyRow } (* NOTE: effect does not matter any more... *)
                    ; codomain } in
                FExpr.at pos ftyp (FExpr.fn Vector.empty var body)
            end else begin
                let pos = body.pos in
                let domain : T.t = Tuple (Vector.map (fun (vars : ExpandPats.final_naming) ->
                    vars.src_var.vtyp
                ) tmp_vars) in
                let ftyp = T.Pi { universals = Vector.empty
                    ; domain = Ior.Right { edomain = domain 
                        ; eff = EmptyRow } (* NOTE: effect does not matter any more... *)
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
                let ftyp = T.Pi { universals = Vector.empty
                    ; domain = Ior.Right { edomain = domain 
                        ; eff = EmptyRow } (* NOTE: effect does not matter any more... *)
                    ; codomain } in
                FExpr.at pos codomain (FExpr.app (FExpr.at pos ftyp (FExpr.use dest)) Vector.empty
                    (FExpr.at pos domain (FExpr.use tmp_var)))
            end else begin
                let domain : T.t = Tuple (Vector.map (fun (vars : ExpandPats.final_naming) ->
                    vars.tmp_var.vtyp
                ) tmp_vars) in
                let ftyp = T.Pi { universals = Vector.empty
                    ; domain = Ior.Right { edomain = domain 
                        ; eff = EmptyRow } (* NOTE: effect does not matter any more... *)
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
        Vector.fold Env.push_val env vars
    ) env defs in
    let pats = Vector.build pats in
    (* OPTIMIZE: Fields accumulator is not needed here, as `_` shows: *)
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
    expand_def vars pos pat expr

(* TODO: Field punning (tricky because the naive translation `letrec x = x in {x = x}` makes no sense) *)
and typeof_record env pos stmts =
    let pats = CCVector.create () in
    let bindings = CCVector.create () in
    let _ = Vector.fold (fun env stmt ->
        let (pat, semiabs, defs', expr) = analyze_field env stmt in
        CCVector.push pats pat;
        CCVector.push bindings (defs', semiabs, expr);
        Vector.fold Env.push_val env defs'
    ) env stmts in
    let pats = Vector.build pats in
    let (env, fields) = Env.push_rec env (CCVector.freeze bindings) in

    let stmts = Source.zip (Source.seq (CCVector.to_seq bindings))
            (Vector.to_source stmts)
        |> Source.zip (Vector.to_source pats)
        |> Stream.from
        |> Stream.flat_map (elaborate_field env)
        |> Stream.into Sink.array in

    let fields = CCVector.of_list !fields in
    CCVector.rev_in_place fields;
    let fields = CCVector.to_array fields in
    let typ = T.Record (Array.fold_left (fun base (var : FExpr.var) ->
        T.With {base; label = var.name; field = var.vtyp}
    ) T.EmptyRow fields) in
    let term = FExpr.at pos typ (FExpr.record (Array.map (fun (var : FExpr.var) ->
        (var.name, FExpr.at pos typ (FExpr.use var))
    ) fields)) in
    {term = FExpr.at pos typ (FExpr.letrec stmts term); eff = T.EmptyRow}

and analyze_field env = function
    | AStmt.Def def -> analyze_def env def
    | AStmt.Expr {v = Var _; pos = _} -> failwith "TODO: field punning"
    | AStmt.Expr expr as field ->
        Env.reportError env expr.pos (Err.InvalidField field);
        let (pat, semiabs, defs) = elaborate_pat env {expr with v = Tuple Vector.empty} in
        (pat, semiabs, defs, {expr with v = Tuple Vector.empty})

and elaborate_field env (pat, ((defs, semiabs, _), stmt)) : FStmt.def Stream.t =
    let (pos, {TS.term = expr; eff}) = match stmt with
        | AStmt.Def (pos, _, expr) ->
            ( pos
            , if Vector.length defs > 0
              then Env.find_rhs env pos (Vector.get defs 0).name
              else implement env semiabs expr )
        | AStmt.Expr {v = Var _; pos = _} -> failwith "TODO: field punning"
        | AStmt.Expr _ -> failwith "unreachable: invalid field in `elaborate_field`" in
    ignore (M.solving_unify expr.pos env eff EmptyRow);
    expand_def defs pos pat expr

and expand_def vars pos (pat : FExpr.pat) expr : FStmt.def Stream.t =
    if Vector.length vars = 1 then begin
        let var = Vector.get vars 0 in
        let typ = var.vtyp in
        let emit_final _ (tmp_vars : ExpandPats.final_naming Vector.t) =
            assert (Vector.length tmp_vars = 1);
            FExpr.at pat.ppos typ (FExpr.use (Vector.get tmp_vars 0).tmp_var) in
        let clauses = Vector.singleton {ExpandPats.pat; emit = emit_final} in
        let destructuring = ExpandPats.expand_clauses pat.ppos typ expr clauses in
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
        let destructuring = ExpandPats.expand_clauses pat.ppos typ expr clauses in
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
                | T.Pi {universals = _; domain = Right {edomain; eff = _}; codomain} ->
                    CCVector.push params edomain;
                    let acc = T.App (acc, (Bv {depth = 0; sibli = i; kind = edomain})) in
                    to_axiom params acc (i + 1) codomain
                | _ -> (axname, Vector.build params, acc, T.Uv impl) in
            to_axiom (CCVector.create ()) (Ov ov) 0 kind
        ) axiom_bindings in
        {term = FExpr.at expr.pos typ (FExpr.axiom axioms term); eff}
    end else check env typ expr

and check : Env.t -> T.t -> AExpr.t with_pos -> FExpr.t typing
= fun env typ expr -> match (typ, expr.v) with
    | (T.Tuple typs, AExpr.Tuple exprs) ->
        let exprs' = CCVector.create () in
        let typs' = CCVector.create () in
        let eff : T.t = Uv (Env.uv env T.aRow) in
        let typ_width = Vector.length typs in
        let expr_width = Vector.length exprs in
        if expr_width = typ_width
        then Vector.iter2 (fun typ expr ->
            let {TS.term = expr; eff = eff'} = check env typ expr in
            CCVector.push exprs' expr;
            CCVector.push typs' expr.typ;
            ignore (M.solving_unify expr.pos env eff' eff)
        ) typs exprs
        else Env.reportError env expr.pos (TupleWidth (typ, typ_width, expr.v, expr_width));
        { term = FExpr.at expr.pos (Tuple (Vector.build typs'))
            (FExpr.values (CCVector.to_array exprs'))
        ; eff }

    | (Pi _, AExpr.Fn clauses) -> check_fn env typ expr.pos clauses

    | _ ->
        let {TS.term = expr; eff} = typeof env expr in
        let Cf coerce = M.solving_subtype expr.pos env expr.typ typ in
        {term = coerce expr; eff}

and check_fn : Env.t -> T.t -> Util.span -> AExpr.clause Vector.t -> FExpr.t typing
= fun env typ pos clauses -> match typ with
    | T.Pi {universals = _; domain; codomain} -> (* FIXME: use `universals` *)
        (match Vector1.of_vector clauses with
        | Some clauses ->
            let clauses = clauses |> Vector1.map (fun clause ->
                let clause = check_clause env domain codomain clause in
                {ExpandPats.pat = clause.FExpr.pat; emit = emit_clause_body clause}
            ) in
            let domain = match domain with
                | Left idomain -> idomain
                | Right {edomain; eff = _} -> edomain
                | Both (idomain, {edomain; eff = _}) ->
                    Tuple (Vector.of_list [idomain; edomain]) in
            let param = FExpr.fresh_var domain in
            let matchee = FExpr.at pos param.vtyp (FExpr.use param) in
            let body = ExpandPats.expand_clauses pos codomain matchee (Vector1.to_vector clauses) in
            { term = FExpr.at pos typ (FExpr.fn (* FIXME: *) Vector.empty param body)
            ; eff = EmptyRow }
        | None -> failwith "TODO: check clauseless fn")
    | _ -> failwith "unreachable: non-Pi `typ` in `check_fn`"

and check_clause env domain codomain {params; body} =
    let ((pat, body_env), eff) = match domain with
        | Ior.Left idomain -> (match params with
            | Left iparam -> (check_param env idomain iparam, T.EmptyRow)
            | _ -> failwith "expected just implicit param")
        | Right {edomain; eff} -> (match params with
            | Right eparam -> (check_param env edomain eparam, eff)
            | _ -> failwith "expected just explicit param")
        | Both (idomain, {edomain; eff}) -> (match params with
            | Both (eparam, iparam) ->
                let (ipat, env) = check_param env idomain iparam in
                let (epat, env) = check_param env edomain eparam in
                ( ({FExpr.ppos = ipat.ppos; pterm = FExpr.TupleP (Vector.of_list [ipat; epat])
                    ; ptyp = Tuple (Vector.of_list [ipat.ptyp; epat.ptyp])}, env)
                , eff )
            | _ -> failwith "expected both implicit and explicit param") in
    let {TS.term = body; eff = body_eff} = check_abs body_env codomain body in
    ignore (M.solving_unify body.pos env body_eff eff);
    {pat; body}

(* # Patterns *)

(* ## Synthesis *)

and elaborate_param env param =
    let (param, (_, typ), vars) = elaborate_pat env param in
    (param, typ, Vector.fold Env.push_val env vars)

and elaborate_pat env pat : FExpr.pat * (T.ov Vector.t * T.t) * FExpr.var Vector.t =
    let elaborate_pats env pats =
        let step (env, pats, typs, defs) pat =
            let (pat, (_, typ), defs') = elaborate_pat env pat in
            let env = Vector.fold Env.push_val env defs' in
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

    | AExpr.Focus _ | App _ | PrimApp _ | Select _ | Record _ ->
        failwith "TODO in elaborate_pat"

    | AExpr.Fn _ ->
        Env.reportError env pat.pos (NonPattern pat.v);
        (* TODO: Treat as `_` instead: *)
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
        let ptyp = T.Uv (Env.uv env kind) in
        let var = FExpr.fresh_var ptyp in
        ( {ppos = pat.pos; pterm = VarP var; ptyp}, (Vector.empty, ptyp)
        , Vector.singleton var )

    | AppSequence _ -> failwith "compiler bug: typechecker encountered AppSequence pattern"

(* ## Checking *)

and check_param env domain param =
    let (param, vars) = check_pat env domain param in
    (param, Vector.fold Env.push_val env vars)

(* TODO: use coercions (and subtyping ?): *)
and check_pat : Env.t -> T.t -> AExpr.pat with_pos -> FExpr.pat * FExpr.var Vector.t
= fun env ptyp pat ->
    let check_pats env domain pats =
        let step (env, pats, defs) domain pat =
            let (pat, defs') = check_pat env domain pat in
            (Vector.fold Env.push_val env defs, pat :: pats, Vector.append defs defs') in
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

    | AExpr.Focus _ | App _ | PrimApp _ | Select _ | Record _ ->
        failwith "TODO in check_pat"

    | AExpr.Fn _ ->
        Env.reportError env pat.pos (NonPattern pat.v);
        ({ppos = pat.pos; pterm = WildP (Name.of_string ""); ptyp}, Vector.empty)

    | AppSequence _ -> failwith "compiler bug: typechecker encountered AppSequence pattern"

(* # Statement Typing *)

let check_stmt : Env.t -> AStmt.t -> FStmt.t Vector.t typing * T.t * Env.t
= fun env -> function
    | AStmt.Def (pos, pat, expr) ->
        let {term = expr; eff} : FExpr.t typing = typeof env expr in
        let (pat, vars) = check_pat env expr.typ pat in
        let defs = expand_def vars pos pat expr
            |> Stream.map (fun def -> FStmt.Def def)
            |> Stream.into (Vector.sink ()) in
        ({term = defs; eff}, expr.typ, Vector.fold Env.push_val env vars)

    | AStmt.Expr expr ->
        let typing = typeof env expr in
        ({typing with term = Vector.singleton (FStmt.Expr typing.term)}, typing.term.typ, env)

end

