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
        (Vector.empty, Vector.empty, T.EmptyRow, T.Proxy (Prim Int))
    | Type ->
        ( Vector.empty, Vector.empty, T.EmptyRow
        , T.Proxy (T.Exists (Vector1.singleton T.aType
            , Proxy (Bv {depth = 0; sibli = 0; kind = T.aType}))) )

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

    | AExpr.Focus (tup, i) ->
        let {TS.term = tup; typ = tup_typ; eff} = typeof env tup in
        (match M.focalize tup.pos env tup_typ (ValuesL (i + 1)) with
        | (Cf coerce, Values typs) when i < Vector.length typs ->
            (* FIXME: coercing potentially nontrivial expr `tup`: *)
            {term = {expr with v = Focus (coerce tup, i)}; typ = Vector.get typs i; eff}
        | _ -> failwith "compiler bug: focusee focalization returned non-tuple")

    | AExpr.Fn clauses -> elaborate_fn env expr.pos clauses

    | AExpr.App (callee, args) ->
        let {TS.term = callee; typ = callee_typ; eff = callee_eff} = typeof env callee in
        (match M.focalize callee.pos env callee_typ (PiL Hole) with
        | (Cf coerce, Pi {universals; domain; codomain}) ->
            let (uvs, domain, codomain) = Env.instantiate_arrow env universals domain codomain in
            (* TODO: DRY: *)
            let arg = check_args env expr.pos domain callee_eff args in
            (match codomain with
            | Exists (existentials, codomain) -> failwith "TODO: existential codomain in App"
            | _ ->
                { term = {expr with v = App (coerce callee, Vector.map (fun uv -> T.Uv uv) uvs, arg)}
                ; typ = codomain
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
        let (domain, {TS.term = clause; typ = codomain; eff}) = elaborate_clause env clause in
        let clauses' = Seq.map (check_clause env domain codomain) clauses' in
        let clauses = Vector.of_seq (fun () -> Seq.Cons (clause, clauses')) in
        let param =
            let domain : T.t = match domain with
                | Ior.Left idomain -> idomain
                | Right {T.edomain; eff = _} -> edomain
                | Both (idomain, {edomain; eff}) ->
                    Values (Vector.of_list [idomain; edomain]) in
            {FExpr.name = Name.fresh (); typ = domain} in
        let param_use = {Util.v = FExpr.Use param.name; pos} in
        let body = {Util.v = FExpr.Match (param_use, clauses); pos} in
        let universals = Vector.map fst (Vector.of_list !universals) in
        let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
            (i + 1, Name.Map.add name i substitution)
        ) (0, Name.Map.empty) universals in
        { TS.term = {Util.v = FExpr.Fn (universals, param, body); pos}
        ; typ = Pi { universals = Vector.map snd universals
                   ; domain = Ior.bimap (Env.close env substitution)
                        (fun {T.edomain; eff} ->
                            { T.edomain = Env.close env substitution edomain
                            ; eff = Env.close env substitution eff })
                        domain
                   ; codomain = Env.close env substitution codomain }
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
            ( {iparam with Util.v = FExpr.ValuesP (Vector.of_list [iparam; eparam])}
            , Both (idomain, edomain), env ) in
    let {TS.term = body; typ = codomain; eff} = typeof env body in
    let domain = match domain with
        | Left idomain ->
            ignore (M.solving_unify body.pos env eff EmptyRow);
            Ior.Left idomain
        | Right edomain -> Right {T.edomain; eff}
        | Both (idomain, edomain) -> Both (idomain, {T.edomain; eff}) in
    (domain, {term = {FExpr.pat; body}; typ = codomain; eff})

and elaborate_param env param =
    let (param, (_, typ), defs) = elaborate_pat env param in
    let env = Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env defs in
    (param, typ, env)

and elaborate_pats env pats =
    let step (pats, typs, defs) pat =
        let (pat, (_, typ), defs') = elaborate_pat env pat in
        (pat :: pats, typ :: typs, Vector.append defs defs') in
    let (pats, typs, defs) = Vector.fold step ([], [], Vector.empty) pats in
    (Vector.of_list (List.rev pats), Vector.of_list (List.rev typs), defs)

and elaborate_pat env pat = match pat.v with
    | AExpr.Values pats when Vector.length pats = 1 -> elaborate_pat env (Vector.get pats 0)

    | AExpr.Values pats ->
        let (pats, typs, defs) = elaborate_pats env pats in
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

    | AExpr.Focus _ | AppSequence _ | App _ | PrimApp _ | Select _ | Record _ ->
        failwith "TODO in elaborate_pat"

    | AExpr.Fn _ ->
        Env.reportError env pat.pos (NonPattern pat.v);
        (* TODO: Treat as `_` instead: *)
        let name = Name.fresh () in
        let kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let typ = T.Uv (Env.uv env kind (Name.fresh ())) in
        ({pat with v = FExpr.UseP name}, (Vector.empty, typ), Vector.singleton {FExpr.name; typ})

(* TODO: DRY: *)
and check_args env pos domain eff args =
    match domain with
    | Ior.Right {T.edomain; eff = app_eff} -> (match args with
        | Ior.Right arg ->
            (* TODO: Effect opening à la Koka: *)
            let _ = M.solving_unify pos env app_eff eff in
            let {TS.term = arg; typ = _; eff = arg_eff} = check env edomain arg in
            let _ = M.solving_unify pos env arg_eff eff in
            arg
        | _ -> failwith "implicit arg passed to purely explicit callee")
    | Left idomain -> (match args with
        | Left arg ->
            (* TODO: Effect opening à la Koka: *)
            let _ = M.solving_unify pos env EmptyRow eff in
            let {TS.term = arg; typ = _; eff = arg_eff} = check env idomain arg in
            let _ = M.solving_unify pos env arg_eff eff in
            arg
        | _ -> failwith "explicit arg passed to purely implicit callee")
    | Both (idomain, {edomain; eff = app_eff}) -> (match args with
        | Both (iarg, earg) ->
            (* TODO: Effect opening à la Koka: *)
            let _ = M.solving_unify pos env app_eff eff in
            let {TS.term = iarg; typ = _; eff = iarg_eff} = check env idomain iarg in
            let _ = M.solving_unify pos env iarg_eff eff in
            let {TS.term = earg; typ = _; eff = earg_eff} = check env edomain earg in
            let _ = M.solving_unify pos env earg_eff eff in
            {iarg with v = Values (Vector.of_list [iarg; earg])}
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
        Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env defs'
    ) env stmts in
    let pats = Vector.build pats in
    let (env, fields) = Env.push_rec env (CCVector.freeze bindings) in

    let stmts = Vector.map3 (elaborate_field env) pats (Vector.build bindings) stmts in

    let fields = CCVector.of_list !fields in
    CCVector.rev_in_place fields;
    let fields = Vector.build fields in
    let term = {Util.v = FExpr.Record (Vector.map (fun (name, _) ->
        (name, {Util.v = FExpr.Use name; pos})
    ) fields); pos} in
    let term = match Vector1.of_vector stmts with
        | Some stmts -> {Util.v = FExpr.Letrec (stmts, term); pos}
        | None -> term in
    let typ = T.Record (Vector.fold (fun base (name, typ) ->
        T.With {base; label = name; field = typ}
    ) T.EmptyRow fields) in
    let eff = T.EmptyRow in
    {term; typ; eff}

and analyze_field env = function
    | AStmt.Def (_, pat, expr) ->
        let (pat, semiabs, defs) = elaborate_pat env pat in
        (pat, semiabs, defs, expr)
    | AStmt.Expr {v = Var _; pos = _} -> failwith "TODO: field punning"
    | AStmt.Expr expr as field ->
        Env.reportError env expr.pos (Err.InvalidField field);
        let (pat, semiabs, defs) = elaborate_pat env {expr with v = Values Vector.empty} in
        (pat, semiabs, defs, {expr with v = Values Vector.empty})

and elaborate_field env pat (defs, semiabs, _) stmt =
    let (pos, {TS.term = expr; typ = _; eff}) = match stmt with
        | AStmt.Def (pos, _, expr) ->
            ( pos
            , if Vector.length defs > 0
              then Env.find_rhs env pos (Vector.get defs 0).name
              else implement env semiabs expr )
        | AStmt.Expr {v = Var _; pos = _} -> failwith "TODO: field punning"
        | AStmt.Expr _ -> failwith "unreachable: invalid field in `elaborate_field`" in
    ignore (M.solving_unify expr.pos env eff EmptyRow);
    (pos, pat, expr)

(* # Checking *)

and check_abs : Env.t -> T.t -> AExpr.t with_pos -> FExpr.t with_pos typing
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
                | T.Pi {universals = _; domain = Right {edomain; eff = _}; codomain} ->
                    CCVector.push params edomain;
                    let acc = T.App (acc, (Bv {depth = 0; sibli = i; kind = edomain})) in
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

    | _ ->
        let {TS.term = expr; typ = expr_typ; eff} = typeof env expr in
        let Cf coerce = M.solving_subtype expr.pos env expr_typ typ in
        {term = coerce expr; typ; eff}

and check_fn : Env.t -> T.t -> Util.span -> AExpr.clause Vector.t -> FExpr.t with_pos typing
= fun env typ pos clauses -> match typ with
    | T.Pi {universals; domain; codomain} ->
        (match Vector1.of_vector clauses with
        | Some clauses ->
            let clauses = Vector1.map (check_clause env domain codomain) clauses in
            let param =
                let domain = match domain with
                    | Left idomain -> idomain
                    | Right {edomain; eff = _} -> edomain
                    | Both (idomain, {edomain; eff = _}) ->
                        Values (Vector.of_list [idomain; edomain]) in
                {FExpr.name = Name.fresh (); typ = domain} in
            let param_use = {Util.v = FExpr.Use param.name; pos} in
            let body = {Util.v = FExpr.Match (param_use, Vector1.to_vector clauses); pos} in
            { term = {v = Fn ((* FIXME: *) Vector.empty, param, body); pos}
            ; typ; eff = EmptyRow }
        | None -> failwith "TODO: check clauseless fn")
    | _ -> failwith "unreachable: non-Pi `typ` in `check_fn`"

and check_clause env domain codomain {params; body} =
    let ((pat, body_env), eff) = match (domain, params) with
        | (Ior.Left idomain, Left iparam) -> (check_param env idomain iparam, T.EmptyRow)
        | (Right {edomain; eff}, Right eparam) -> (check_param env edomain eparam, eff)
        | (Both (idomain, {edomain; eff}), Both (eparam, iparam)) ->
            let (ipat, env) = check_param env idomain iparam in
            let (epat, env) = check_param env edomain eparam in
            ( ({ipat with Util.v = FExpr.ValuesP (Vector.of_list [ipat; epat])}, env)
            , eff ) in
    let {TS.term = body; typ = _; eff = body_eff} = check_abs body_env codomain body in
    ignore (M.solving_unify body.pos env body_eff eff);
    {pat; body}

and check_param env domain param =
    let (param, defs) = check_pat env domain param in
    let env = Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env defs in
    (param, env)

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

    | AExpr.Focus _ | AppSequence _ | App _ | PrimApp _ | Select _ | Record _ ->
        failwith "TODO in check_pat"

    | AExpr.Fn _ ->
        Env.reportError env pat.pos (NonPattern pat.v);
        (* TODO: Treat as `_` instead: *)
        let name = Name.fresh () in
        ({pat with v = UseP name}, Vector.singleton {FExpr.name; typ})

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

