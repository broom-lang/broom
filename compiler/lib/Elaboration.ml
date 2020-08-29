module Make (C : TyperSigs.TYPING) (M : TyperSigs.MATCHING) : TyperSigs.ELABORATION = struct

module AType = Ast.Type
module T = Fc.Type
module Err = TypeError

type 'a with_pos = 'a Util.with_pos

let reabstract = Environmentals.reabstract

let elaborate : Env.t -> AType.t with_pos -> T.abs = fun env typ ->
    let rec elab env (typ : AType.t with_pos) =
        match typ.v with
        (*| AType.Pi ({name; typ = domain}, eff, codomain) ->
            let domain = kindcheck env domain in
            let (env, universals, domain_locator, domain) = Env.push_domain_skolems env domain in
            let name = match name with
                | Some name -> name
                | None -> Name.fresh () in
            let env = Env.push_domain env {name; typ = domain} domain_locator in

            let ubs = Vector.map fst universals in
            let ukinds = Vector.map snd ubs in
            let (codomain_locator, codomain) =
                match (eff, kindcheck env codomain) with
                | (Pure, Exists (existentials, codomain_locator, concr_codo)) ->
                    let substitution = Vector.map (fun kind ->
                        let kind = match Vector1.of_vector ukinds with
                            | Some ukinds ->
                                (match kind with (* TODO: Is this sufficient to ensure unique reprs?: *)
                                | ArrowK (ukinds', kind) -> ArrowK (Vector1.append ukinds' ukinds, kind)
                                | _ -> ArrowK (ukinds, kind))
                            | None -> kind in
                        let ov = Env.generate env (Name.freshen name, kind) in
                        (match Vector1.of_vector universals with
                        | Some universals -> App (Ov ov, Vector1.map (fun ov -> Ov ov) universals)
                        | None -> Ov ov)
                    ) existentials in
                    ( expose_locator substitution codomain_locator
                    , to_abs (expose substitution concr_codo) )
                | (_, codomain) -> (Hole, codomain) in

            (match Vector1.of_vector ubs with
            | Some universals1 ->
                let (_, substitution) = Vector1.fold_left (fun (i, substitution) (name, _) ->
                    (i + 1, Name.Map.add name i substitution)
                ) (0, Name.Map.empty) universals1 in
                ( PiL (ukinds, eff, close_locator substitution codomain_locator)
                , Pi ( ukinds, close_locator substitution domain_locator
                     , close substitution domain, eff, close_abs substitution codomain ) )
            | None ->
                ( PiL (ukinds, eff, codomain_locator)
                , Pi (ukinds, domain_locator, domain, eff, codomain) ))*)

        | Record decls ->
            if Vector.length decls = 0
            then (T.Hole, T.Record EmptyRow)
            else failwith "TODO: nonempty signature"

        (*| AType.Sig decls ->
            let env = Env.push_sig env decls in
            let (locators, decls) = Vector.split (Vector.map (elab_decl env) decls) in
            (RecordL locators, Record decls)*)

        | AType.Path expr ->
            let {TyperSigs.term = _; typ = proxy_typ; eff} = C.typeof env {typ with v = expr} in
            let _ = M.solving_unify typ.pos env eff EmptyRow in
            (match M.focalize typ.pos env proxy_typ (TypeL (Uv (Env.uv env (Name.fresh ())))) with
            | (_, Type typ) ->
                let (_, locator, typ) = reabstract env typ in
                (locator, typ)
            | _ -> failwith "unreachable")

        (*| AType.Singleton expr ->
            (match C.typeof env expr with
            | {term = _; typ; eff = Pure} -> (Hole, typ)
            | _ -> raise (TypeError (typ.pos, ImpureType expr.v)))*)

        (*| AType.Type ->
            let ov = Env.generate env (Name.fresh (), TypeK) in
            (TypeL (Ov ov), Type (to_abs (Ov ov)))*)

        | AType.Prim pt -> (T.Hole, T.Prim pt)

    (*and elab_decl env {name; typ} =
        let (locator, {name; typ}) = C.lookup typ.pos env name in
        let label = Name.to_string name in
        ({label; typ = locator}, {label; typ}*) in

    let (env, params) = Env.push_existential env in
    let (locator, typ) = elab env typ in
    let (_, substitution) = List.fold_left (fun (i, substitution) (name, _) ->
        (i + 1, Name.Map.add name i substitution)
    ) (0, Name.Map.empty) (!params) in
    Exists ( Vector.map snd (Vector.of_list (!params))
           , T.close_locator (Env.uv_substr env) substitution locator
           , T.close (Env.uv_substr env) substitution typ )

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
        | (Pi _ | Record _ | Type _ | Prim _) as typ -> Some (typ, None)
        | Bv _ -> failwith "unreachable: `Bv` in `whnf`"
        | Use _ -> failwith "unreachable: `Use` in `whnf`"

    and apply callee args = match callee with
        | T.Fn body -> eval (T.expose (Env.uv_substr env) (Vector1.to_vector args) body)
        | Ov _ | App _ -> Some (T.App (callee, args), None)
        | Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ -> None
            | Assigned _ -> failwith "unreachable: Assigned in `apply`.")
        | Pi _ | Record _ | Type _ | Prim _ -> failwith "unreachable: uncallable type in `whnf`"
        | Bv _ -> failwith "unreachable: `Bv` in `whnf/apply`"
        | Use _ -> failwith "unreachable: `Use` in `whnf/apply`"
    in eval typ
end

