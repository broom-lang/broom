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
    | Int -> T.aType
    | Array -> Pi {universals = Vector.empty; idomain = None; edomain = T.aType
        ; eff = EmptyRow; codomain = T.aType}
    | SingleRep -> T.aType
    | Boxed -> Prim SingleRep
    | TypeIn -> Pi {universals = Vector.empty; idomain = None; edomain = T.rep
        ; eff = EmptyRow; codomain = T.aType}
    | RowOf -> Pi {universals = Vector.empty; idomain = None; edomain = T.aKind
        ; eff = EmptyRow; codomain = T.aKind}

let rec kindof_F pos env : T.t -> T.kind = function
    | Exists (_, body) -> kindof_F pos env body
    | PromotedArray typs ->
        let el_kind = if Vector.length typs = 0
            then kindof_F pos env (Vector.get typs 0)
            else Uv (Env.uv env T.aKind (Name.fresh ())) in
        App (Prim Array, el_kind)
    | PromotedValues typs -> Values (Vector.map (kindof_F pos env) typs)
    | Values typs ->
        let kinds = Vector.map (kindof_F pos env) typs in
        App (Prim TypeIn, PromotedArray kinds)
    | Pi _ | Record _ | Proxy _ -> T.aType
    | With _ | EmptyRow -> T.aRow
    | Fn (domain, body) ->
        Pi { universals = Vector.empty; idomain = None; edomain = domain
            ; eff = EmptyRow; codomain = kindof_F pos env body }
    | App (callee, arg) ->
        (match kindof_F pos env callee with
        | Pi {universals; idomain; edomain = domain; eff; codomain} ->
            check_F pos env domain arg;
            codomain
        | _ -> failwith "unreachable: invalid type application in `kindof_F`.")
    | Ov ((_, kind), _) -> kind
    | Bv {kind; _} -> kind
    | Uv uv -> (match Env.get_uv env uv with
        | Unassigned (_, kind, _) -> kind
        | Assigned typ -> kindof_F pos env typ)
    | Prim pt -> kindof_prim pt

and check_F pos env kind typ =
    let kind' = kindof_F pos env typ in
    ignore (M.solving_unify pos env kind' kind)

let rec kindof : Env.t -> AType.t with_pos -> T.t kinding = fun env typ ->
    let rec elab env (typ : AType.t with_pos) : T.t kinding =
        match typ.v with
        | Values typs ->
            let kinds = CCVector.create () in
            let typs = Vector.map (fun typ ->
                let {TS.typ; kind} = elab env typ in
                CCVector.push kinds kind;
                typ
            ) typs in
            {typ = Values typs; kind = App (Prim TypeIn, PromotedArray (Vector.build kinds))}

        | Pi {idomain; edomain; eff; codomain} -> elab_pi env idomain edomain eff codomain

        | Record decls ->
            let {TS.typ = row; kind = row_kind} = elab_row env typ.pos decls in
            let typ' = T.Record row in
            {typ = typ'; kind = kindof_F typ.pos env typ'}

        | Row decls -> elab_row env typ.pos decls

        | Path expr ->
            let pos = typ.pos in
            let {TS.term = _; typ = proxy_typ; eff} = C.typeof env {typ with v = expr} in
            let _ = M.solving_unify typ.pos env eff EmptyRow in
            (* FIXME: does not accept e.g. `row`: *)
            (match M.focalize typ.pos env proxy_typ (ProxyL (Prim Int)) with
            | (_, Proxy typ) ->
                let (_, typ) = reabstract env typ in
                {typ; kind = kindof_F pos env typ}
            | _ -> failwith "unreachable")

        (*| AType.Singleton expr ->
            (match C.typeof env expr with
            | {term = _; typ; eff = Pure} -> (Hole, typ)
            | _ -> Env.reportError env typ.pos (ImpureType expr.v))*)

        | Prim pt -> {typ = Prim pt; kind = kindof_prim pt}

    and elab_pi env0 idomain edomain eff codomain =
        let (env, universals) = Env.push_existential env0 in
        let (idomain, env) = match idomain with
            | Some idomain ->
                let (idomain, env) = elab_domain env idomain in
                (Some idomain, env)
            | None -> (None, env) in
        let (edomain, env) = elab_domain env edomain in (* FIXME: make non-dependent (by default) *)
        let eff : T.t = check env T.aRow eff in
        let codomain_kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep (Name.fresh ()))) in
        let codomain = check env codomain_kind codomain in
        let universals = Vector.of_list !universals in

        let ubs = Vector.map fst universals in
        let ukinds = Vector.map snd ubs in
        let codomain =
            match (eff, codomain) with (* FIXME: eval `eff` *)
            | (EmptyRow, Exists (existentials, concr_codo)) ->
                (* Hoist codomain existentials to make applicative functor (in the ML modules sense): *)
                let substitution = Vector.map (fun kind ->
                    let kind = Vector.fold_right (fun codomain domain ->
                        T.Pi { universals = Vector.empty; idomain = None
                            ; edomain = domain; eff = EmptyRow; codomain = codomain }
                    ) kind ukinds in
                    let ov = Env.generate env0 (Name.fresh (), kind) in
                    Vector.fold (fun callee arg -> T.App (callee, Ov arg)) (Ov ov) universals
                ) (Vector1.to_vector existentials) in
                Env.expose env0 substitution concr_codo
            | (_, codomain) -> codomain in

        let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
            (i + 1, Name.Map.add name i substitution)
        ) (0, Name.Map.empty) ubs in
        { TS.typ = T.Pi { universals = Vector.map snd ubs
             ; idomain = Option.map (Env.close env substitution) idomain
             ; edomain = Env.close env substitution edomain
             ; eff = Env.close env substitution eff
             ; codomain = Env.close env substitution codomain }
        ; kind = T.aType }

    and elab_domain env (domain : AExpr.t with_pos) =
        let (_, (_, domain), defs) = C.elaborate_pat env domain in
        let env = Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ)
            env defs in
        (domain, env)

    and elab_row env pos decls =
        let bindings = CCVector.create () in
        let _ = Vector.fold (fun env decl ->
            let (_, semiabs, defs', rhs) = analyze_decl env decl in
            CCVector.push bindings (defs', semiabs, rhs);
            Vector.fold (fun env {FExpr.name; typ} -> Env.push_val env name typ) env defs'
        ) env decls in
        let (env, fields) = Env.push_row env (CCVector.freeze bindings) in

        Vector.iter2 (elaborate_field env) (Vector.build bindings) decls;

        let row = List.fold_right (fun (name, typ) base ->
            T.With {base; label = name; field = typ}
        ) (!fields) EmptyRow in
        {typ = row; kind = kindof_F pos env row}

    and analyze_decl env = function
        | AStmt.Def (_, pat, expr) ->
            let (pat, semiabs, defs') = C.elaborate_pat env pat in
            let expr' = AExpr.App ({expr with v = Var (Name.of_string "typeof")}, expr) in
            (pat, semiabs, defs', {expr with v = AType.Path expr'})
        | AStmt.Expr {v = Ann (pat, typ); pos = _} ->
            let (pat, semiabs, defs') = C.elaborate_pat env pat in
            (pat, semiabs, defs', typ)
        | AStmt.Expr expr as decl ->
            Env.reportError env expr.pos (Err.InvalidDecl decl);
            let (pat, semiabs, defs') = C.elaborate_pat env {expr with v = Values Vector.empty} in
            (pat, semiabs, defs', {expr with v = AType.Values Vector.empty})

    and elaborate_field env (defs, (existentials, lhs), rhs) decl =
        let pos = AStmt.pos decl in
        ignore (
            if Vector.length defs > 0
            then Env.find_rhst env pos (Vector.get defs 0).FExpr.name
            else begin
                let {TS.typ = rhs; kind = _} as kinding = kindof env rhs in
                let (existentials', rhs) = reabstract env rhs in
                ignore (M.solving_subtype pos env rhs lhs);
                kinding
            end) in

    let (env, params) = Env.push_existential env in
    let {TS.typ; kind} = elab env typ in
    let typ : T.t = match Vector1.of_list !params |> Option.map (Vector1.map fst) with
        | Some params ->
            let (_, substitution) = Vector1.fold (fun (i, substitution) (name, _) ->
                (i + 1, Name.Map.add name i substitution)
            ) (0, Name.Map.empty) params in
            Exists (Vector1.map snd params, Env.close env substitution typ)
        | None -> typ in
    {typ; kind}

and check env kind ({v = _; pos} as typ) =
    let {TS.typ; kind = kind'} = kindof env typ in
    ignore (M.solving_unify pos env kind' kind);
    typ

and eval env typ =
    let (let*) = Option.bind in
    let (let+) = Fun.flip Option.map in

    let rec eval = function
        | T.App (callee, arg) ->
            let* (callee, callee_co) = eval callee in
            let+ (typ, co) = apply callee arg in
            ( typ
            , match (callee_co, co) with
              | (Some callee_co, Some co) ->
                  Some (T.Trans (Inst (callee_co, Vector1.singleton arg), co))
              | (Some callee_co, None) -> Some (Inst (callee_co, Vector1.singleton arg))
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
        | ( Exists _ | PromotedArray _ | PromotedValues _
          | Values _ | Pi _ | Record _ | With _ | EmptyRow | Proxy _ | Prim _ ) as typ -> Some (typ, None)
        | Bv _ -> failwith "unreachable: `Bv` in `eval`"

    and apply callee arg = match callee with
        (* NOTE: Arg kinds do not need to be checked here because all `App`s originate from functors: *)
        | T.Fn (param, body) -> eval (Env.expose env (Vector.singleton arg) body)
        | Ov _ | App _ | Prim _ -> Some (T.App (callee, arg), None)
        | Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ -> None
            | Assigned _ -> failwith "unreachable: Assigned in `apply`.")
        | Exists _ | PromotedArray _ | PromotedValues _
        | Values _ | Pi _ | Record _ | With _ | EmptyRow | Proxy _ ->
            failwith "unreachable: uncallable type in `eval/apply`"
        | Bv _ -> failwith "unreachable: `Bv` in `eval/apply`"
    in eval typ
end

