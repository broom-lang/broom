open Asserts

module TS = TyperSigs
module Uv = ComplexFc.Types.Uv

module Make (Env : TS.ENV)
    (C : TS.TYPING with type env = Env.t)
    (M : TS.MATCHING with type env = Env.t)
: TS.KINDING with type env = Env.t
= struct

module AType = Ast.Type
module T = ComplexFc.Type
module AExpr = Ast.Term.Expr
(*module AStmt = Ast.Term.Stmt
module FExpr = Fc.Term.Expr
module Err = TypeError*)

type env = Env.t
type 'a with_pos = 'a Util.with_pos

let (!) = TxRef.(!)

let kindof_prim : Prim.t -> T.kind = function
    | Int | Bool | String -> T.aType
    | Array | Cell -> Pi {domain = T.aType; eff = EmptyRow; codomain = T.aType}
    | SingleRep -> T.aType
    | Boxed -> Prim SingleRep
    | TypeIn -> Pi {domain = T.rep; eff = EmptyRow; codomain = T.aType}
    | RowOf -> Pi {domain = T.aKind; eff = EmptyRow; codomain = T.aKind}

let rec kindof_F pos env : T.t -> T.kind = function
    | PromotedArray typs ->
        let el_kind = if Vector.length typs > 0
            then kindof_F pos env (Vector.get typs 0)
            else Env.tv env T.aKind in
        App (Prim Array, el_kind)
    | PromotedTuple typs -> Tuple (Vector.map (kindof_F pos env) typs)
    | Tuple typs -> (* FIXME: nested tuples *)
        let kinds = Vector.map (kindof_F pos env) typs in
        App (Prim TypeIn, PromotedArray kinds)
    | Pi _ | Impli _ | Record _ | Proxy _ -> T.aType
    | With _ | EmptyRow -> T.aRow
    | Fn {param; body} ->
        Pi {domain = param; eff = EmptyRow; codomain = kindof_F pos env body }
    | App (callee, arg) ->
        (match kindof_F pos env callee with
        | Pi {domain; eff = _; codomain} -> (* FIXME: universals *)
            check_F pos env domain arg;
            codomain
        | _ -> unreachable (Some pos) ~msg: "invalid type application in `kindof_F`.")
    | Uv {Uv.bound; _} -> (match !bound with
        | Bot kind -> kind
        | Flex typ | Rigid typ -> kindof_F pos env typ)
    | Ov {kind; _} -> kind
    | Prim pt -> kindof_prim pt

and check_F pos env kind typ =
    let kind' = kindof_F pos env typ in
    M.unify pos env kind' kind

(*let rec kindof : Env.t -> AType.t with_pos -> T.t kinding = fun env typ ->
    let rec elab env (typ : AType.t with_pos) : T.t kinding =
        match typ.v with
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
    {typ; kind}*)

let rec eval =
    let (let* ) = Option.bind in
    let (let+) = Fun.flip Option.map in

    let rec eval_forced pos env t = match t with
        | T.App (callee, arg) ->
            let* (callee, callee_co) = eval pos env callee in
            let+ (typ, co) = apply pos callee arg in
            ( typ
            , match (callee_co, co) with
              | (Some _, Some _) ->
                  (*Some (T.Trans (Inst (callee_co, Vector1.singleton arg), co))*)
                  todo (Some pos)
              | (Some _, None) ->
                  (*Some (Inst (callee_co, Vector1.singleton arg))*)
                  todo (Some pos)
              | (None, Some co) -> Some co
              | (None, None) -> None )

        | Ov _ ->
            (*match Env.get_implementation env ov with
            | Some (axname, _, uv) ->
                let typ = T.Uv uv in
                let+ (typ, co) = eval typ in
                ( typ
                , match co with
                  | Some co -> Some (T.Trans (AUse axname, co))
                  | None -> Some (AUse axname) )
            | None -> Some (typ, None)*)
            Some (t, None)
        | Uv _ | Pi _ | Impli _ | Fn _ | Tuple _ | PromotedArray _ | PromotedTuple _
        | Record _ | With _ | EmptyRow | Proxy _ | Prim _ -> Some (t, None)

    and apply pos callee arg = match callee with
        (* NOTE: Arg kinds do not need to be checked here because all `App`s originate from functors: *)
        (*| T.Fn {param = _; body} -> eval (Env.expose env (Vector.singleton arg) body)*)
        | T.Fn _ -> todo (Some pos)
        | Ov _ | App _ | Prim _ -> Some (T.App (callee, arg), None)
        | Uv _ -> None
        | Pi _ | Impli _ | Tuple _ | PromotedArray _ | PromotedTuple _
        | Record _ | With _ | EmptyRow | Proxy _ ->
            unreachable (Some pos) ~msg: "uncallable type in `eval.apply`" in

    fun pos env t -> eval_forced pos env (T.force t)

let rec kindof_nonquantifying env scope (typ : AType.t with_pos) = match typ.v with
    | Pi {domain; eff; codomain} ->
        let env0 = env in
        let (env, scope') = Env.push_level env0 in
        let (domain, env) = elab_domain env scope' domain in
        let eff : T.t = match eff with
            | Some eff -> check_nonquantifying env scope T.aRow eff
            | None -> EmptyRow in
        let codomain_kind = T.App (Prim TypeIn, Env.tv env T.rep) in
        let codomain = check_nonquantifying env scope codomain_kind codomain in

        (*let codomain =
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
            | (_, codomain) -> codomain in*)

        Uv.Scope.exit scope scope';
        Env.forall_scope_ovs env scope' (Pi {domain; eff; codomain})

    | Impli {domain; codomain} ->
        let env0 = env in
        let (env, scope') = Env.push_level env0 in
        let (domain, env) = elab_domain env scope' domain in
        let codomain_kind = T.App (Prim TypeIn, Env.tv env T.rep) in
        let codomain = check_nonquantifying env scope codomain_kind codomain in

        (*let codomain =
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
            | codomain -> codomain in*)

        Uv.Scope.exit scope scope';
        Env.forall_scope_ovs env scope' (Impli {domain; codomain})

    | Tuple typs -> Tuple (Vector.map (kindof_nonquantifying env scope) typs)

    | Path expr ->
        let carrie = Env.tv env (Env.tv env T.aType) in
        let {TS.term = _; eff} = C.check env (T.Proxy carrie) {typ with v = expr} in
        M.unify typ.pos env eff EmptyRow;
        Env.reabstract typ.pos env scope carrie

    | Prim pt -> kindof_prim pt

    | _ -> todo (Some typ.pos) ~msg: "check_nonquantifying"

and elab_domain env scope (domain : AExpr.t with_pos) =
    let (pat, defs) = C.elaborate_pat env scope domain in
    let env = Vector.fold (Env.push_val Explicit) env defs in
    (pat.ptyp, env)

and check_nonquantifying env scope _ (typ : AType.t with_pos) =
    let t = kindof_nonquantifying env scope typ in
    (*M.unify typ.pos env (kindof_F typ.pos env t) kind;*)
    t

let kindof env0 t =
    let (env, scope) = Env.push_level env0 in
    let t = kindof_nonquantifying env scope t in
    Uv.Scope.exit (Env.t_scope env0) scope;
    Env.exists_scope_ovs env scope t

let check env0 kind t =
    let (env, scope) = Env.push_level env0 in
    let t = check_nonquantifying env scope kind t in
    Uv.Scope.exit (Env.t_scope env0) scope;
    Env.exists_scope_ovs env scope t

end

