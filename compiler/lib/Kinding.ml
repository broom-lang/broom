module TS = TyperSigs

module Make (Env : TS.ENV)
    (C : TS.TYPING with type env = Env.t)
    (M : TS.MATCHING with type env = Env.t)
: TS.KINDING with type env = Env.t
= struct

module AType = Ast.Type
module T = Fc.Type
module AExpr = Ast.Term.Expr
module AStmt = Ast.Term.Stmt
module FExpr = Fc.Term.Expr
module Err = TypeError

type env = Env.t
type 'a with_pos = 'a Util.with_pos
type 'a kinding = 'a TS.kinding

let reabstract = Env.reabstract
let (!) = TxRef.(!)

let kindof_prim : Prim.t -> T.kind = function
    | Int -> Prim Type
    | Type | Row -> Prim Type

let rec kindof_F env : T.t -> T.kind = function
    | Pi _ | Record _ | Proxy _ -> Prim Type
    | With _ | EmptyRow -> Prim Row
    | Fn (domain, body) ->
        Pi (Vector.empty, Vector1.to_vector domain, EmptyRow, T.to_abs (kindof_F env body))
    | App (callee, args) ->
        (match kindof_F env callee with
        | Pi (universals, domain, eff, Exists (existentials, codomain)) ->
            Vector.iter2 (fun domain arg -> check_F env domain arg)
                domain (Vector1.to_vector args);
            codomain)
    | Ov ((_, kind), _) -> kind
    | Bv {kind; _} -> kind
    | Uv uv -> (match Env.get_uv env uv with
        | Unassigned (_, kind, _) -> kind
        | Assigned typ -> kindof_F env typ)
    | Prim pt -> kindof_prim pt

and check_F env kind typ =
    let kind' = kindof_F env typ in
    if kind' = kind (* HACK *)
    then ()
    else failwith "check_F: inequal kinds"

let rec kindof : Env.t -> AType.t with_pos -> T.abs kinding = fun env typ ->
    let rec elab env (typ : AType.t with_pos) : T.t kinding =
        match typ.v with
        | Pi {idomain; edomain; eff; codomain} -> elab_pi env idomain edomain eff codomain

        | Record decls ->
            let {TS.typ = row; kind = row_kind} = elab_row env typ.pos decls in
            {typ = T.Record row; kind = Prim Type}

        | Row decls -> elab_row env typ.pos decls

        | Path expr ->
            let {TS.term = _; typ = proxy_typ; eff} = C.typeof env {typ with v = expr} in
            let _ = M.solving_unify typ.pos env eff EmptyRow in
            (* FIXME: does not accept e.g. `row`: *)
            (match M.focalize typ.pos env proxy_typ (ProxyL (Uv (Env.uv env (Prim Type) (Name.fresh ())))) with
            | (_, Proxy typ) ->
                let (_, typ) = reabstract env typ in
                {typ; kind = kindof_F env typ}
            | _ -> failwith "unreachable")

        (*| AType.Singleton expr ->
            (match C.typeof env expr with
            | {term = _; typ; eff = Pure} -> (Hole, typ)
            | _ -> raise (TypeError (typ.pos, ImpureType expr.v)))*)

        | Prim pt -> {typ = Prim pt; kind = kindof_prim pt}

    and elab_pi env0 idomain edomain eff codomain =
        let (env, universals) = Env.push_existential env0 in
        let (idomain, env) = elab_domain env idomain in
        let (edomain, env) = elab_domain env edomain in (* FIXME: make non-dependent (by default) *)
        let T.Exists (effixtentials, eff) = check env (T.Prim Row) eff in
        let codomain = check env (T.Prim Type) codomain in
        let universals = Vector.of_list !universals in

        let ubs = Vector.map fst universals in
        let ukinds = Vector.map snd ubs in
        let codomain =
            match (eff, codomain) with (* FIXME: eval `eff` *)
            | (EmptyRow, Exists (existentials, concr_codo)) ->
                (* Hoist codomain existentials to make applicative functor (in the ML modules sense): *)
                let substitution = Vector.map (fun kind ->
                    let kind = match Vector1.of_vector ukinds with
                        | Some ukinds ->
                            (match kind with (* TODO: Is this sufficient to ensure unique reprs?: *)
                            | T.Pi (universals, ukinds', eff, kind) ->
                                T.Pi (universals, Vector.append ukinds' (Vector1.to_vector ukinds), eff, kind)
                            | _ -> T.Pi (Vector.empty, Vector1.to_vector ukinds, EmptyRow, T.to_abs kind))
                        | None -> kind in
                    let ov = Env.generate env0 (Name.fresh (), kind) in
                    (match Vector1.of_vector universals with
                    | Some universals -> T.App (Ov ov, Vector1.map (fun ov -> T.Ov ov) universals)
                    | None -> Ov ov)
                ) existentials in
                T.to_abs (Env.expose env0 substitution concr_codo)
            | (_, codomain) -> codomain in

        let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
            (i + 1, Name.Map.add name i substitution)
        ) (0, Name.Map.empty) ubs in
        { TS.typ = T.Pi ( Vector.map snd ubs
             , Vector.map (Env.close env substitution) (Vector.append idomain edomain)
             , Env.close env substitution eff
             , Env.close_abs env substitution codomain )
        ; kind = Prim Type }

    and elab_domain env (domain : AExpr.t with_pos) =
        let domain = match domain.v with
            | AExpr.Values domain -> domain
            | _ -> Vector.singleton domain in
        let (domain, env) = Vector.fold (fun (domain, env) pat ->
            let (pat, (_, typ), defs) = C.elaborate_pat env pat in
            let env = Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ)
                env defs in
            (typ :: domain, env)
        ) ([], env) domain in
        let domain = Vector.of_list (List.rev domain) in
        (domain, env)

    and elab_row env pos decls =
        let (pat_typs, defs, env) = Vector.fold (fun (semiabsen, defs, env) decl ->
            let (pat, semiabs, defs') = analyze_decl env decl in
            let env = Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ)
                env defs' in
            (semiabs :: semiabsen, Vector.append defs defs', env))
            ([], Vector.empty, env) decls in
        let pat_typs = Vector.of_list (List.rev pat_typs) in

        Vector.iter2 (fun decl (_, super) ->
            let {TS.typ; kind} = elab_decl env decl in
            ignore (M.solving_subtype pos env typ super)
        ) decls pat_typs;

        let row = Vector.fold (fun base {FExpr.name; typ} ->
            T.With {base; label = name; field = typ}
        ) EmptyRow defs in
        {typ = row; kind = Prim Row}

    and analyze_decl env = function
        | AStmt.Def (_, pat, _) -> C.elaborate_pat env pat
        | AStmt.Expr {v = Ann (pat, _); pos = _} -> C.elaborate_pat env pat
        | AStmt.Expr expr as decl -> raise (Err.TypeError (expr.pos, Err.InvalidDecl decl))

    and elab_decl env = function
        | AStmt.Def (_, _, expr) ->
            let expr' = AExpr.App ({expr with v = Var (Name.of_string "typeof")}, Vector.singleton expr) in
            elab env {expr with v = Path expr'}
        | AStmt.Expr {v = Ann (_, typ); pos = _} -> elab env typ
        | AStmt.Expr expr as decl -> raise (Err.TypeError (expr.pos, Err.InvalidDecl decl)) in

    let (env, params) = Env.push_existential env in
    let {TS.typ; kind} = elab env typ in
    let params = !params |> Vector.of_list |> Vector.map fst in
    let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
        (i + 1, Name.Map.add name i substitution)
    ) (0, Name.Map.empty) params in
    { typ = Exists (Vector.map snd params, Env.close env substitution typ)
    ; kind }

and check env kind typ =
    let {TS.typ; kind = kind'} = kindof env typ in
    if kind' = kind (* HACK *)
    then typ
    else failwith "inequal kinds"

and eval env typ =
    let (let*) = Option.bind in
    let (let+) = Fun.flip Option.map in

    let rec eval = function
        | T.App (callee, args) ->
            let* (callee, callee_co) = eval callee in
            let+ (typ, co) = apply callee args in
            ( typ
            , match (callee_co, co) with
              | (Some callee_co, Some co) -> Some (T.Trans (Inst (callee_co, args), co))
              | (Some callee_co, None) -> Some (Inst (callee_co, args))
              | (None, Some co) -> Some co
              | (None, None) -> None )
        | Fn _ as typ -> Some (typ, None)
        | Ov ov as typ ->
            (match Env.get_implementation env ov with
            | Some (axname, _, uv) ->
                let typ = T.Uv uv in
                let+ (typ, co) = eval typ in
                ( typ
                , match co with
                  | Some co -> Some (T.Trans (AUse axname, co))
                  | None -> Some (AUse axname) )
            | None -> Some (typ, None))
        | Uv uv as typ ->
            (match Env.get_uv env uv with
            | Assigned typ -> eval typ
            | Unassigned _ -> Some (typ, None))
        | (Values _ | Pi _ | Record _ | With _ | EmptyRow | Proxy _ | Prim _) as typ -> Some (typ, None)
        | Bv _ -> failwith "unreachable: `Bv` in `whnf`"

    and apply callee args = match callee with
        | T.Fn (params, body) -> (* FIXME: Check arg kinds *)
            eval (Env.expose env (Vector1.to_vector args) body)
        | Ov _ | App _ -> Some (T.App (callee, args), None)
        | Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ -> None
            | Assigned _ -> failwith "unreachable: Assigned in `apply`.")
        | Values _ | Pi _ | Record _ | With _ | EmptyRow | Proxy _ | Prim _ ->
            failwith "unreachable: uncallable type in `whnf`"
        | Bv _ -> failwith "unreachable: `Bv` in `whnf/apply`"
    in eval typ
end

