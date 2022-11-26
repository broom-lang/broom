open Asserts

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
    | Int | Bool | String -> T.aType
    | Array | Cell -> Pi {universals = Vector.empty; domain = T.aType; eff = EmptyRow
        ; codomain = T.aType}
    | SingleRep -> T.aType
    | Boxed -> Prim SingleRep
    | TypeIn -> Pi {universals = Vector.empty; domain = T.rep; eff = EmptyRow
        ; codomain = T.aType}
    | RowOf -> Pi {universals = Vector.empty; domain = T.aKind; eff = EmptyRow
        ; codomain = T.aKind}

let rec kindof_F pos env : T.t -> T.kind = function
    | Exists (_, body) -> kindof_F pos env body
    | PromotedArray typs ->
        let el_kind = if Vector.length typs > 0
            then kindof_F pos env (Vector.get typs 0)
            else Uv (Env.uv env T.aKind) in
        App (Prim Array, el_kind)
    | PromotedTuple typs -> Tuple (Vector.map (kindof_F pos env) typs)
    | Tuple typs ->
        let kinds = Vector.map (kindof_F pos env) typs in
        App (Prim TypeIn, PromotedArray kinds)
    | Pi _ | Impli _ | Record _ | Proxy _ -> T.aType
    | With _ | EmptyRow -> T.aRow
    | Fn (domain, body) -> Pi { universals = Vector.empty; domain; eff = EmptyRow
        ; codomain = kindof_F pos env body }
    | App (callee, arg) ->
        (match kindof_F pos env callee with
        | Pi {universals; domain; eff = _; codomain} ->
            if Vector.length universals = 0 then begin
                check_F pos env domain arg;
                codomain
            end else todo (Some pos) ~msg: "universals in type application"
        | _ -> unreachable (Some pos) ~msg: "invalid type application in `kindof_F`.")
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
        | Tuple typs ->
            let kinds = CCVector.create () in
            let typs = Vector.map (fun typ ->
                let {TS.typ; kind} = elab env typ in
                CCVector.push kinds kind;
                typ
            ) typs in
            {typ = Tuple typs; kind = App (Prim TypeIn, PromotedArray (Vector.build kinds))}

        | Pi {domain; eff; codomain} ->
            let env0 = env in
            let (env, universals) = Env.push_existential env0 in
            let (domain, env) = elab_domain env domain in
            let eff : T.t = match eff with
                | Some eff -> check env T.aRow eff
                | None -> EmptyRow in
            let codomain_kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
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
                            T.Pi {universals = Vector.empty; domain; eff = EmptyRow; codomain}
                        ) kind ukinds in
                        let ov = Env.generate env0 (Name.fresh (), kind) in
                        Vector.fold (fun callee arg -> T.App (callee, Ov arg)) (Ov ov) universals
                    ) (Vector1.to_vector existentials) in
                    Env.expose env0 substitution concr_codo
                | (_, codomain) -> codomain in

            let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
                (i + 1, Name.Map.add name i substitution)
            ) (0, Name.Map.empty) ubs in
            { TS.typ = T.Pi {universals = Vector.map snd ubs
                 ; domain = Env.close env substitution domain
                 ; eff = Env.close env substitution eff
                 ; codomain = Env.close env substitution codomain }
            ; kind = T.aType }

        | Impli {domain; codomain} ->
            let env0 = env in
            let (env, universals) = Env.push_existential env0 in
            let (domain, env) = elab_domain env domain in
            let codomain_kind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
            let codomain = check env codomain_kind codomain in
            let universals = Vector.of_list !universals in

            let ubs = Vector.map fst universals in
            let ukinds = Vector.map snd ubs in
            let codomain =
                match codomain with (* FIXME: eval `eff` *)
                | Exists (existentials, concr_codo) ->
                    (* Hoist codomain existentials to make applicative functor (in the ML modules sense): *)
                    let substitution = Vector.map (fun kind ->
                        let kind = Vector.fold_right (fun codomain domain ->
                            T.Pi {universals = Vector.empty; domain; eff = EmptyRow; codomain}
                        ) kind ukinds in
                        let ov = Env.generate env0 (Name.fresh (), kind) in
                        Vector.fold (fun callee arg -> T.App (callee, Ov arg)) (Ov ov) universals
                    ) (Vector1.to_vector existentials) in
                    Env.expose env0 substitution concr_codo
                | codomain -> codomain in

            let (_, substitution) = Vector.fold (fun (i, substitution) (name, _) ->
                (i + 1, Name.Map.add name i substitution)
            ) (0, Name.Map.empty) ubs in
            { TS.typ = T.Impli {universals = Vector.map snd ubs
                 ; domain = Env.close env substitution domain
                 ; codomain = Env.close env substitution codomain }
            ; kind = T.aType }

        | Declare (decls, body) ->
            let bindings = CCVector.create () in
            let _ = Vector1.fold (fun env decl ->
                let (_, semiabs, defs', rhs) = analyze_decl env decl in
                CCVector.push bindings (defs', semiabs, rhs);
                Vector.fold (Env.push_val Explicit) env defs'
            ) env decls in
            (* OPTIMIZE: Fields accumulator is not needed here, as `_` shows: *)
            (* FIXME: fields accumulator was used to put fields in dependency order! *)
            let (env, _) = Env.push_row env (CCVector.freeze bindings) in

            Vector1.iter2 (elaborate_decl env)
                (Vector.build bindings |> Vector1.of_vector |> Option.get)
                decls;

            elab env body

        | Record decls ->
            let {TS.typ = row; kind = _} = elab_row env typ.pos decls in
            let typ' = T.Record row in
            {typ = typ'; kind = kindof_F typ.pos env typ'}

        | Row decls -> elab_row env typ.pos decls

        | Path expr ->
            let carrie =
                let kind = T.Uv (Env.uv env T.aType) in
                T.Uv (Env.uv env kind) in
            let {TS.term = _; eff} = C.check env (T.Proxy carrie) {typ with v = expr} in
            let _ = M.solving_unify typ.pos env eff EmptyRow in
            let (_, carrie) = reabstract env carrie in
            {typ = carrie; kind = kindof_F typ.pos env carrie}

        (*| AType.Singleton expr ->
            (match C.typeof env expr with
            | {term = _; typ; eff = Pure} -> (Hole, typ)
            | _ -> Env.reportError env typ.pos (ImpureType expr.v))*)

        | Prim pt -> {typ = Prim pt; kind = kindof_prim pt}

    and elab_domain env (domain : AExpr.t with_pos) =
        let (_, (_, domain), defs) = C.elaborate_pat env domain in
        let env = Vector.fold (Env.push_val Explicit) env defs in
        (domain, env)

    and elab_row env pos decls =
        let row = Vector.fold_right (fun base -> function
            | AType.Decl (_, {v = Var label; _}, typ) ->
                let {TS.typ = field; kind = _} = elab env typ in
                T.With {base; label; field}
            | _ -> bug (Some pos) ~msg: "bad record type field reached typechecker"
        ) EmptyRow decls in
        {typ = row; kind = kindof_F pos env row}

    and analyze_decl env = function
        | AType.Def (_, pat, expr) ->
            let (pat, semiabs, defs') = C.elaborate_pat env pat in
            let expr' = AExpr.PrimApp (TypeOf, None, expr) in
            (pat, semiabs, defs', {expr with v = AType.Path expr'})
        | Decl (_, pat, typ) ->
            let (pat, semiabs, defs') = C.elaborate_pat env pat in
            (pat, semiabs, defs', typ)

    and elaborate_decl env (defs, (_, lhs), rhs) decl =
        let pos = AType.Decl.pos decl in
        ignore (
            if Vector.length defs > 0
            then Env.find_rhst env pos (Vector.get defs 0).FExpr.name
            else begin
                let {TS.typ = rhs; kind = _} as kinding = kindof env rhs in
                let (_, rhs) = reabstract env rhs in
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

and eval pos env typ =
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
        | ( Exists _ | PromotedArray _ | PromotedTuple _
          | Tuple _ | Pi _ | Impli _ | Record _ | With _ | EmptyRow | Proxy _ | Prim _ ) as typ ->
            Some (typ, None)
        | Bv _ -> unreachable (Some pos) ~msg: "`Bv` in `eval`"

    and apply callee arg = match callee with
        (* NOTE: Arg kinds do not need to be checked here because all `App`s originate from functors: *)
        | T.Fn (_, body) -> eval (Env.expose env (Vector.singleton arg) body)
        | Ov _ | App _ | Prim _ -> Some (T.App (callee, arg), None)
        | Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ -> None
            | Assigned _ -> unreachable (Some pos) ~msg: "Assigned in `apply`.")
        | Exists _ | PromotedArray _ | PromotedTuple _
        | Tuple _ | Pi _ | Impli _ | Record _ | With _ | EmptyRow | Proxy _ ->
            unreachable (Some pos) ~msg: "uncallable type in `eval.apply`"
        | Bv _ -> unreachable (Some pos) ~msg: "`Bv` in `eval.apply`"
    in eval typ
end

