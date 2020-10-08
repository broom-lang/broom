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

let primop_typ =
    let open Primop in
    function
    | IAdd | ISub | IMul ->
        ( Vector.empty, Vector.of_list [T.Prim Int; T.Prim Int]
        , T.EmptyRow, T.Prim Prim.Int )
    | Int ->
        (Vector.empty, Vector.empty, T.EmptyRow, T.Proxy (Prim Int))
    | Type ->
        ( Vector.empty, Vector.empty, T.EmptyRow
        , T.Proxy (T.Exists (Vector1.singleton T.aType
            , Proxy (Bv {depth = 0; sibli = 0; kind = T.aType}))) )

let rec typeof : Env.t -> AExpr.t with_pos -> FExpr.t typing
= fun env expr -> match expr.v with
    | AExpr.Values exprs when Vector.length exprs = 1 -> typeof env (Vector.get exprs 0)

    | AExpr.Values exprs ->
        let exprs' = CCVector.create () in
        let typs = CCVector.create () in
        let eff : T.t = Uv (Env.uv env T.aRow (Name.fresh ())) in
        exprs |> Vector.iter (fun expr ->
            let {TS.term = expr; eff = eff'} = typeof env expr in
            CCVector.push exprs' expr;
            CCVector.push typs expr.typ;
            ignore (M.solving_unify expr.pos env eff' eff)
        ); 
        { term = { term = Values (CCVector.to_array exprs')
                 ; typ = Values (Vector.build typs); pos = expr.pos; parent = None }
        ; eff }

    | AExpr.Focus (tup, index) ->
        let {TS.term = tup; eff} = typeof env tup in
        (match M.focalize tup.pos env tup.typ (ValuesL (index + 1)) with
        | (Cf coerce, Values typs) when index < Vector.length typs ->
            (* FIXME: coercing potentially nontrivial expr `tup`: *)
            { term = { term = Focus {focusee = coerce tup; index}; typ = Vector.get typs index
            ; pos = expr.pos; parent = None }; eff }
        | _ -> failwith "compiler bug: focusee focalization returned non-tuple")

    | AExpr.Fn clauses -> elaborate_fn env expr.pos clauses

    | AExpr.App (callee, args) ->
        let {TS.term = callee; eff = callee_eff} = typeof env callee in
        (match M.focalize callee.pos env callee.typ (PiL Hole) with
        | (Cf coerce, Pi {universals; domain; codomain}) ->
            let (uvs, domain, codomain) = Env.instantiate_arrow env universals domain codomain in
            let arg = check_args env expr.pos domain callee_eff args in
            (match codomain with
            | Exists (existentials, codomain) -> failwith "TODO: existential codomain in App"
            | _ ->
                { term = { term = App {callee = coerce callee; universals = Vector.map (fun uv -> T.Uv uv) uvs; arg}
                    ; typ = codomain; pos = expr.pos; parent = None }
                ; eff = callee_eff })
        | _ -> failwith "compiler bug: callee focalization returned non-function")

    | AExpr.AppSequence exprs -> (* TODO: in/pre/postfix parsing, special forms, macros *)
        let callee = Vector1.get exprs 0 in
        let args = Vector.sub (Vector1.to_vector exprs) 1 (Vector1.length exprs - 1) in
        let arg = if Vector.length args = 1
            then Vector.get args 0
            else {expr with v = Values args} in
        typeof env {expr with v = AExpr.App (callee, Right arg)}

    | AExpr.PrimApp (op, args) ->
        let (universals, domain, app_eff, codomain) = primop_typ op in
        let (uvs, domain, codomain) =
            Env.instantiate_arrow env universals (Right {edomain = Values domain; eff = app_eff})
                codomain in
        let arg = check_args env expr.pos domain app_eff args in
        { term = { term = PrimApp {op; universals = Vector.map (fun uv -> T.Uv uv) uvs; arg}
            ; typ = codomain; pos = expr.pos; parent = None }
        ; eff = app_eff }

    | AExpr.Record stmts -> typeof_record env expr.pos stmts

    | AExpr.Select (selectee, label) -> (* TODO: lacks-constraint: *)
        let field : T.t = Uv (Env.uv env T.aType (Name.fresh ())) in
        let typ : T.t = Record (With {base = Uv (Env.uv env T.aRow (Name.fresh ())); label; field}) in
        let {TS.term = selectee; eff} = check env typ selectee in
        {TS.term = {term = Select {selectee; label}; typ = field; pos = expr.pos; parent = None}; eff}

    | AExpr.Ann (expr, typ) ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let typ = K.check env kind typ in
        (* FIXME: Abstract type generation effect *)
        check_abs env typ expr

    | AExpr.Proxy typ ->
        let {TS.typ; kind} = K.kindof env {v = typ; pos = expr.pos} in
        {term = FExpr.at expr.pos (Proxy typ) (Proxy typ); eff = EmptyRow}

    | AExpr.Var name ->
        let {FExpr.vtyp = typ; _} as var = Env.find env expr.pos name in
        { term = FExpr.at expr.pos typ (FExpr.use var)
        ; eff = EmptyRow }

    | AExpr.Const c ->
        {term = FExpr.at expr.pos (const_typ c) (Const c); eff = EmptyRow}

and elaborate_fn : Env.t -> Util.span -> AExpr.clause Vector.t -> FExpr.t typing
= fun env pos clauses -> match Vector.to_seq clauses () with
    | Cons (clause, clauses') ->
        let (env, universals) = Env.push_existential env in
        let (domain, {TS.term = clause; eff}) = elaborate_clause env clause in
        let codomain = clause.FExpr.body.typ in
        let clauses' = Seq.map (check_clause env domain codomain) clauses' in
        let clauses = Vector.of_seq (fun () -> Seq.Cons (clause, clauses')) in
        let domain_t : T.t = match domain with
            | Ior.Left idomain -> idomain
            | Right {T.edomain; eff = _} -> edomain
            | Both (idomain, {edomain; eff}) ->
                Values (Vector.of_list [idomain; edomain]) in
        let param = FExpr.fresh_var domain_t None in
        let matchee = FExpr.at pos param.vtyp (FExpr.use param) in
        let body = FExpr.at pos codomain (FExpr.Match {matchee; clauses}) in
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
            (FExpr.Fn {universals; param; body})
        ; eff = EmptyRow }
    | Nil -> failwith "TODO: clauseless fn"

and elaborate_clause env {params; body} =
    let (pat, domain, env) = match params with
        | Left ipat ->
            let (param, domain, env) = elaborate_param env ipat in
            (param, Ior.Left domain, env)
        | Right epat ->
            let (param, domain, env) = elaborate_param env epat in
            (param, Right domain, env)
        | Both (ipat, epat) ->
            let (iparam, idomain, env) = elaborate_param env ipat in
            let (eparam, edomain, env) = elaborate_param env epat in
            ( { FExpr.ppos = iparam.ppos; pterm = FExpr.ValuesP (Vector.of_list [iparam; eparam])
                ; ptyp = Values (Vector.of_list [iparam.ptyp; eparam.ptyp]) }
            , Both (idomain, edomain), env ) in
    let {TS.term = body; eff} = typeof env body in
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
            FExpr.at iarg.pos (Values (Vector.of_list [iarg.typ; earg.typ]))
                (Values (Array.of_list [iarg; earg]))
        | Right earg -> failwith "TODO: Both App args"
        | Left _ -> failwith "missing explicit arg")

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
        |> Stream.into (Vector.sink ()) in

    let fields = CCVector.of_list !fields in
    CCVector.rev_in_place fields;
    let fields = CCVector.to_array fields in
    let typ = T.Record (Array.fold_left (fun base (var : FExpr.var) ->
        T.With {base; label = var.name; field = var.vtyp}
    ) T.EmptyRow fields) in
    let term = FExpr.at pos typ (FExpr.Record (Array.map (fun (var : FExpr.var) ->
        (var.name, FExpr.at pos typ (FExpr.use var))
    ) fields)) in
    {term = FExpr.at pos typ (FExpr.letrec stmts term); eff = T.EmptyRow}

and analyze_field env = function
    | AStmt.Def (_, pat, expr) ->
        let (pat, semiabs, defs) = elaborate_pat env pat in
        (pat, semiabs, defs, expr)
    | AStmt.Expr {v = Var _; pos = _} -> failwith "TODO: field punning"
    | AStmt.Expr expr as field ->
        Env.reportError env expr.pos (Err.InvalidField field);
        let (pat, semiabs, defs) = elaborate_pat env {expr with v = Values Vector.empty} in
        (pat, semiabs, defs, {expr with v = Values Vector.empty})

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
    elaborate_def env defs pos pat expr

and elaborate_def env defs pos (pat : FExpr.pat) expr : FStmt.def Stream.t =
    let typ : T.t = Values (Vector.map (fun (var : var) -> var.vtyp) defs) in
    let body = FExpr.at pat.ppos typ (Values (Stream.from (Vector.to_source defs)
        |> Stream.map (fun (var : var) -> FExpr.at pat.ppos var.vtyp (FExpr.use var))
        |> Stream.into (Sink.buffer (Vector.length defs)))) in
    let clauses = Vector.singleton {FExpr.pat; body} in
    let destructuring = ExpandPats.expand_clauses pat.ppos typ expr clauses in
    let tuple_var = FExpr.fresh_var typ (Some destructuring) in
    Stream.prepend (pos, tuple_var, destructuring)
        (Stream.from (Vector.to_source defs)
            |> Stream.indexed
            |> Stream.map (fun (index, (var : var)) ->
                let focusee = FExpr.at pat.ppos tuple_var.vtyp (FExpr.use tuple_var) in
                (pos, var, FExpr.at pat.ppos var.vtyp (FExpr.Focus {focusee; index}))))

(* # Checking *)

and check_abs : Env.t -> T.t -> AExpr.t with_pos -> FExpr.t typing
= fun env typ expr -> implement env (Env.reabstract env typ) expr

and implement : Env.t -> T.ov Vector.t * T.t -> AExpr.t with_pos -> FExpr.t typing
= fun env (existentials, typ) expr ->
    match Vector1.of_vector existentials with
    | Some existentials ->
        let axiom_bindings = Vector1.map (fun (((name, kind), _) as param) ->
            (Name.fresh (), param, Env.uv env kind name)
        ) existentials in
        let env = Env.push_axioms env axiom_bindings in
        let {TS.term; eff} = check env typ expr in
        let axioms = Vector1.map (fun (axname, (((_, kind), _) as ov), impl) ->
            let rec to_axiom params acc i = function
                | T.Pi {universals = _; domain = Right {edomain; eff = _}; codomain} ->
                    CCVector.push params edomain;
                    let acc = T.App (acc, (Bv {depth = 0; sibli = i; kind = edomain})) in
                    to_axiom params acc (i + 1) codomain
                | _ -> (axname, Vector.build params, acc, T.Uv impl) in
            to_axiom (CCVector.create ()) (Ov ov) 0 kind
        ) axiom_bindings in
        {term = FExpr.at expr.pos typ (Axiom {axioms; body = term}); eff}
    | None -> check env typ expr

and check : Env.t -> T.t -> AExpr.t with_pos -> FExpr.t typing
= fun env typ expr -> match (typ, expr.v) with
    | (T.Values typs, AExpr.Values exprs) ->
        let exprs' = CCVector.create () in
        let typs' = CCVector.create () in
        let eff : T.t = Uv (Env.uv env T.aRow (Name.fresh ())) in
        (* FIXME: raises on length mismatch: *)
        Vector.iter2 (fun typ expr ->
            let {TS.term = expr; eff = eff'} = check env typ expr in
            CCVector.push exprs' expr;
            CCVector.push typs' expr.typ;
            ignore (M.solving_unify expr.pos env eff' eff)
        ) typs exprs;
        { term = FExpr.at expr.pos (Values (Vector.build typs'))
            (Values (CCVector.to_array exprs'))
        ; eff }

    | (Pi _, AExpr.Fn clauses) -> check_fn env typ expr.pos clauses

    | _ ->
        let {TS.term = expr; eff} = typeof env expr in
        let Cf coerce = M.solving_subtype expr.pos env expr.typ typ in
        {term = coerce expr; eff}

and check_fn : Env.t -> T.t -> Util.span -> AExpr.clause Vector.t -> FExpr.t typing
= fun env typ pos clauses -> match typ with
    | T.Pi {universals; domain; codomain} ->
        (match Vector1.of_vector clauses with
        | Some clauses ->
            let clauses = Vector1.map (check_clause env domain codomain) clauses in
            let domain = match domain with
                | Left idomain -> idomain
                | Right {edomain; eff = _} -> edomain
                | Both (idomain, {edomain; eff = _}) ->
                    Values (Vector.of_list [idomain; edomain]) in
            let param = FExpr.fresh_var domain None in
            let matchee = FExpr.at pos param.vtyp (FExpr.use param) in
            let body = FExpr.at pos codomain (FExpr.Match {matchee; clauses = Vector1.to_vector clauses}) in
            { term = FExpr.at pos typ (Fn {universals = (* FIXME: *) Vector.empty; param; body})
            ; eff = EmptyRow }
        | None -> failwith "TODO: check clauseless fn")
    | _ -> failwith "unreachable: non-Pi `typ` in `check_fn`"

and check_clause env domain codomain {params; body} =
    let ((pat, body_env), eff) = match (domain, params) with
        | (Ior.Left idomain, Left iparam) -> (check_param env idomain iparam, T.EmptyRow)
        | (Right {edomain; eff}, Right eparam) -> (check_param env edomain eparam, eff)
        | (Both (idomain, {edomain; eff}), Both (eparam, iparam)) ->
            let (ipat, env) = check_param env idomain iparam in
            let (epat, env) = check_param env edomain eparam in
            ( ({FExpr.ppos = ipat.ppos; pterm = FExpr.ValuesP (Vector.of_list [ipat; epat])
                ; ptyp = Values (Vector.of_list [ipat.ptyp; epat.ptyp])}, env)
            , eff ) in
    let {TS.term = body; eff = body_eff} = check_abs body_env codomain body in
    ignore (M.solving_unify body.pos env body_eff eff);
    {pat; body}

(* # Patterns *)

(* ## Synthesis *)

and elaborate_param env param =
    let (param, (_, typ), defs) = elaborate_pat env param in
    (param, typ, Vector.fold Env.push_val env defs)

and elaborate_pat env pat : FExpr.pat * (T.ov Vector.t * T.t) * FExpr.var Vector.t =
    let elaborate_pats env pats =
        let step (env, pats, typs, defs) pat =
            let (pat, (_, typ), defs') = elaborate_pat env pat in
            let env = Vector.fold Env.push_val env defs' in
            (env, pat :: pats, typ :: typs, Vector.append defs defs') in
        let (_, pats, typs, defs) = Vector.fold step (env, [], [], Vector.empty) pats in
        (Vector.of_list (List.rev pats), Vector.of_list (List.rev typs), defs) in

    match pat.v with
    | AExpr.Values pats when Vector.length pats = 1 -> elaborate_pat env (Vector.get pats 0)

    | AExpr.Values pats ->
        let (pats, typs, defs) = elaborate_pats env pats in
        let ptyp : T.t = Values typs in
        ({ppos = pat.pos; pterm = FExpr.ValuesP pats; ptyp}, (Vector.empty, ptyp), defs)

    | AExpr.Ann (pat, typ) ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let typ = K.check env kind typ in
        let (_, typ) as semiabs = Env.reabstract env typ in
        let (pat, defs) = check_pat env typ pat in
        (pat, semiabs, defs)

    | AExpr.Var name ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let ptyp = T.Uv (Env.uv env kind (Name.fresh ())) in
        let var = FExpr.var name ptyp None in
        ({ppos = pat.pos; pterm = VarP var; ptyp}, (Vector.empty, ptyp), Vector.singleton var)

    | AExpr.Proxy carrie ->
        let {TS.typ = carrie; kind} = K.kindof env {pat with v = carrie} in
        let ptyp : T.t = Proxy carrie in
        ({ppos = pat.pos; pterm = ProxyP carrie; ptyp}, (Vector.empty, ptyp), Vector.empty)

    | AExpr.Const c ->
        let ptyp = const_typ c in
        ({ppos = pat.pos; pterm = ConstP c; ptyp}, (Vector.empty, ptyp), Vector.empty)

    | AExpr.Focus _ | AppSequence _ | App _ | PrimApp _ | Select _ | Record _ ->
        failwith "TODO in elaborate_pat"

    | AExpr.Fn _ ->
        Env.reportError env pat.pos (NonPattern pat.v);
        (* TODO: Treat as `_` instead: *)
        let name = Name.fresh () in
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let ptyp = T.Uv (Env.uv env kind (Name.fresh ())) in
        let var = FExpr.var name ptyp None in
        ( {ppos = pat.pos; pterm = VarP var; ptyp}, (Vector.empty, ptyp)
        , Vector.singleton var )

(* ## Checking *)

and check_param env domain param =
    let (param, defs) = check_pat env domain param in
    (param, Vector.fold Env.push_val env defs)

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
    | AExpr.Values pats when Vector.length pats = 1 -> check_pat env ptyp (Vector.get pats 0)

    | AExpr.Values pats ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let typs = Vector.map (fun _ -> T.Uv (Env.uv env kind (Name.fresh ()))) pats in
        let _ = M.solving_unify pat.pos env ptyp (Values typs) in
        let (pats, defs) = check_pats env typs pats in
        ({ppos = pat.pos; pterm = FExpr.ValuesP pats; ptyp}, defs)

    | AExpr.Ann (pat', typ') ->
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let typ' = K.check env kind typ' in
        let (_, typ') = Env.reabstract env typ' in
        let _ = M.solving_unify pat.pos env ptyp typ' in
        check_pat env typ' pat'

    | AExpr.Var name ->
        let var = FExpr.var name ptyp None in
        ({ppos = pat.pos; pterm = VarP var; ptyp}, Vector.singleton var)

    | AExpr.Proxy carrie ->
        let {TS.typ = carrie; kind} = K.kindof env {pat with v = carrie} in
        let _ = M.solving_unify pat.pos env ptyp (Proxy carrie) in
        ({ppos = pat.pos; pterm = ProxyP carrie; ptyp}, Vector.empty)

    | AExpr.Const c ->
        let _ = M.solving_unify pat.pos env ptyp (const_typ c) in
        ({ppos = pat.pos; pterm = ConstP c; ptyp}, Vector.empty)

    | AExpr.Focus _ | AppSequence _ | App _ | PrimApp _ | Select _ | Record _ ->
        failwith "TODO in check_pat"

    | AExpr.Fn _ ->
        Env.reportError env pat.pos (NonPattern pat.v);
        ({ppos = pat.pos; pterm = WildP; ptyp}, Vector.empty)

(* # Statement Typing *)

let deftype _ = failwith "TODO: deftype"

let check_stmt : Env.t -> AStmt.t -> FStmt.t Vector.t typing * T.t * Env.t
= fun env -> function
    | AStmt.Def (pos, pat, expr) ->
        let {term = expr; eff} : FExpr.t typing = typeof env expr in
        let (pat, vars) = check_pat env expr.typ pat in
        let defs = elaborate_def env vars pos pat expr
            |> Stream.map (fun def -> FStmt.Def def)
            |> Stream.into (Vector.sink ()) in
        ({term = defs; eff}, expr.typ, Vector.fold Env.push_val env vars)

    | AStmt.Expr expr ->
        let typing = typeof env expr in
        ({typing with term = Vector.singleton (FStmt.Expr typing.term)}, typing.term.typ, env)

(* # Lookup *)

let lookup _ = failwith "TODO: lookup"

end

