module Make (C : TyperSigs.TYPING) (M : TyperSigs.MATCHING) : TyperSigs.ELABORATION = struct

module AType = Ast.Type
module T = Fc.Type
module AExpr = Ast.Term.Expr
module AStmt = Ast.Term.Stmt
module FExpr = Fc.Term.Expr
module Err = TypeError

type 'a with_pos = 'a Util.with_pos

let reabstract = Environmentals.reabstract
let (!) = TxRef.(!)

let rec elaborate : Env.t -> AType.t with_pos -> T.abs = fun env typ ->
    let rec elab env (typ : AType.t with_pos) =
        match typ.v with
        | Pi {idomain; edomain; eff; codomain} -> elab_pi env idomain edomain eff codomain

        | Record decls -> T.Record (elab_row env typ.pos decls)

        | Row decls -> elab_row env typ.pos decls

        | Path expr ->
            let {TyperSigs.term = _; typ = proxy_typ; eff} = C.typeof env {typ with v = expr} in
            let _ = M.solving_unify typ.pos env eff EmptyRow in
            (match M.focalize typ.pos env proxy_typ (TypeL (Uv (Env.uv env (Name.fresh ())))) with
            | (_, Type typ) ->
                let (_, typ) = reabstract env typ in
                typ
            | _ -> failwith "unreachable")

        (*| AType.Singleton expr ->
            (match C.typeof env expr with
            | {term = _; typ; eff = Pure} -> (Hole, typ)
            | _ -> raise (TypeError (typ.pos, ImpureType expr.v)))*)

        | Prim pt -> Prim pt

    and elab_pi env0 idomain edomain eff codomain = (* TODO: Applicative functors: *)
        let (env, universals) = Env.push_existential env0 in
        let (idomain, env) = elab_domain env idomain in
        let (edomain, env) = elab_domain env edomain in (* FIXME: make non-dependent (by default) *)
        let Exists (effixtentials, eff) = elaborate env eff in
        let codomain = elaborate env codomain in
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
                            | T.ArrowK (ukinds', kind) -> T.ArrowK (Vector1.append ukinds' ukinds, kind)
                            | _ -> T.ArrowK (ukinds, kind))
                        | None -> kind in
                    let ov = Env.generate env0 (Name.fresh (), kind) in
                    (match Vector1.of_vector universals with
                    | Some universals -> T.App (Ov ov, Vector1.map (fun ov -> T.Ov ov) universals)
                    | None -> Ov ov)
                ) existentials in
                T.to_abs (Environmentals.expose env0 substitution concr_codo)
            | (_, codomain) -> codomain in

        let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
            (i + 1, Name.Map.add name i substitution)
        ) (0, Name.Map.empty) ubs in
        T.Pi ( Vector.map snd ubs
             , Vector.map (Environmentals.close env substitution) (Vector.append idomain edomain)
             , Environmentals.close env substitution eff
             , Environmentals.close_abs env substitution codomain )

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
            let typ = elab_decl env decl in
            ignore (M.solving_subtype pos env typ super)
        ) decls pat_typs;

        let row = Vector.fold (fun base {FExpr.name; typ} ->
            T.With {base; label = name; field = typ}
        ) EmptyRow defs in
        row

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
    let typ = elab env typ in
    let params = !params |> Vector.of_list |> Vector.map fst in
    let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
        (i + 1, Name.Map.add name i substitution)
    ) (0, Name.Map.empty) params in
    Exists (Vector.map snd params, Environmentals.close env substitution typ)

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
        | (Values _ | Pi _ | Record _ | With _ | EmptyRow | Type _ | Prim _) as typ -> Some (typ, None)
        | Bv _ -> failwith "unreachable: `Bv` in `whnf`"
        | Use _ -> failwith "unreachable: `Use` in `whnf`"

    and apply callee args = match callee with
        | T.Fn body -> eval (Environmentals.expose env (Vector1.to_vector args) body)
        | Ov _ | App _ -> Some (T.App (callee, args), None)
        | Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ -> None
            | Assigned _ -> failwith "unreachable: Assigned in `apply`.")
        | Values _ | Pi _ | Record _ | With _ | EmptyRow | Type _ | Prim _ ->
            failwith "unreachable: uncallable type in `whnf`"
        | Bv _ -> failwith "unreachable: `Bv` in `whnf/apply`"
        | Use _ -> failwith "unreachable: `Use` in `whnf/apply`"
    in eval typ
end

