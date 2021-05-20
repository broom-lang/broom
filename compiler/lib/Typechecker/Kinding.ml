open Asserts

module TS = TyperSigs
module Env = TypeEnv
module AExpr = Ast.Expr
module ADecl = Ast.Decl
module T = Fc.Type
module FExpr = Fc.Term.Expr
open Transactional.Ref

type 'a kinding = 'a TS.kinding

module Make
    (Constraints : TS.CONSTRAINTS)
    (Typing : TS.TYPING)
= struct
    let kindof_prim : Prim.t -> T.kind = function
        | Unit -> (* TypeIn UnitRep *)
            App {callee = Prim TypeIn; arg = Prim UnitRep}

        | Int | Bool | String -> T.aType
        | Array | Cell -> Pi {universals = Vector.empty; domain = T.aType; eff = EmptyRow
            ; codomain = T.aType}
        | Rep -> T.aType
        | Boxed -> Prim Rep

        | UnitRep -> Prim Rep
        | PairRep -> (* Rep -> Rep -> Rep *)
            Pi {universals = Vector.empty; domain = Prim Rep; eff = EmptyRow
                ; codomain = Pi {universals = Vector.empty; domain = Prim Rep; eff = EmptyRow
                    ; codomain = Prim Rep}}

        | TypeIn -> (* Rep -> Type *)
            Pi {universals = Vector.empty; domain = Prim Rep; eff = EmptyRow
                ; codomain = T.aType}

        | RowOf -> Pi {universals = Vector.empty; domain = T.aKind; eff = EmptyRow
            ; codomain = T.aKind}

    let rec kindof_F ctrs span env : T.t -> T.kind = function
        | Exists {existentials = _; body} -> kindof_F ctrs span env body
        | Pi _ | Impli _ | Record _ | Variant _ | Proxy _ -> T.aType

        | Pair {fst; snd} -> (* TypeIn (PairRep fst_rep snd_rep) *)
            let fst_rep = T.Uv (Env.uv env false (Prim Rep)) in
            check_F ctrs span env (T.App {callee = Prim TypeIn; arg = fst_rep}) fst;
            let snd_rep = T.Uv (Env.uv env false (Prim Rep)) in
            check_F ctrs span env (T.App {callee = Prim TypeIn; arg = snd_rep}) snd;
            let rep = T.App {callee = App {callee = Prim PairRep; arg = fst_rep}; arg = snd_rep} in
            App {callee = Prim TypeIn; arg = rep}

        | With _ | EmptyRow -> T.aRow
        | Fn {param = domain; body} -> Pi { universals = Vector.empty; domain; eff = EmptyRow
            ; codomain = kindof_F ctrs span env body }
        | App {callee; arg} ->
            (match kindof_F ctrs span env callee with
            | Pi {universals; domain; eff = _; codomain} ->
                if Vector.length universals = 0 then begin
                    check_F ctrs span env domain arg;
                    codomain
                end else todo (Some span) ~msg: "universals in type application"
            | _ -> unreachable (Some span) ~msg: "invalid type application in `kindof_F`.")
        | Ov _ -> todo (Some span) (*((_, kind), _) -> kind*)
        | Bv _ -> todo (Some span) (*{kind; _} -> kind*)
        | Uv uv -> (match !uv with
            | Unassigned (_, _, kind, _) -> kind
            | Assigned typ -> kindof_F ctrs span env typ)
        | Prim pt -> kindof_prim pt

    and check_F ctrs span env kind typ =
        let kind' = kindof_F ctrs span env typ in
        ignore (Constraints.unify ctrs span env kind' kind)

    let repof_F ctrs span env typ = match kindof_F ctrs span env typ with
        | App {callee = Prim TypeIn; arg = rep} -> rep
        | _ -> todo (Some span)

    let elaborate ctrs env (typ : AExpr.t) =
        let rec elab env (typ : AExpr.t) : T.t kinding =
            match typ.v with
            | PiT {domain; eff; codomain} ->
                let env0 = env in
                let (env, universals) = Env.push_existential env0 in
                let (domain, env) = elab_domain env domain in
                let eff : T.t = match eff with
                    | Some eff -> check env T.aRow eff
                    | None -> EmptyRow in
                let codomain_kind = Env.some_type_kind env false in
                let codomain = check env codomain_kind codomain in
                let universals = Vector.of_list !universals in

                let ukinds = Vector.map (fun {T.kind; _} -> kind) universals in
                let codomain =
                    match (eff, codomain) with (* FIXME: eval `eff` *)
                    | (EmptyRow, Exists {existentials; body = concr_codo}) ->
                        (* Hoist codomain existentials to make applicative functor (in the ML modules sense): *)
                        let substitution = Vector.map (fun kind ->
                            let kind = Vector.fold_right (fun codomain domain ->
                                T.Pi {universals = Vector.empty; domain; eff = EmptyRow; codomain}
                            ) kind ukinds in
                            let ov = Env.generate env0 (Name.fresh (), kind) in
                            Vector.fold (fun callee arg -> T.App {callee; arg = Ov arg})
                                (Ov ov) universals
                        ) (Vector1.to_vector existentials) in
                        T.expose substitution concr_codo
                    | (_, codomain) -> codomain in

                let (_, substitution) = Vector.fold (fun (i, substitution) {T.name; _} ->
                    (i + 1, Name.Map.add name i substitution)
                ) (0, Name.Map.empty) universals in
                { TS.typ = T.Pi {universals = Vector.map (fun {T.kind; _} -> kind) universals
                     ; domain = T.close substitution domain
                     ; eff = T.close substitution eff
                     ; codomain = T.close substitution codomain }
                ; kind = T.aType }

            | ImpliT {domain; codomain} ->
                let env0 = env in
                let (env, universals) = Env.push_existential env0 in
                let (domain, env) = elab_domain env domain in
                let codomain_kind = Env.some_type_kind env false in
                let codomain = check env codomain_kind codomain in
                let universals = Vector.of_list !universals in

                let ukinds = Vector.map (fun {T.kind; _} -> kind) universals in
                let codomain =
                    match codomain with (* FIXME: eval `eff` *)
                    | Exists {existentials; body = concr_codo} ->
                        (* Hoist codomain existentials to make applicative functor (in the ML modules sense): *)
                        let substitution = Vector.map (fun kind ->
                            let kind = Vector.fold_right (fun codomain domain ->
                                T.Pi {universals = Vector.empty; domain; eff = EmptyRow; codomain}
                            ) kind ukinds in
                            let ov = Env.generate env0 (Name.fresh (), kind) in
                            Vector.fold (fun callee arg -> T.App {callee; arg = Ov arg})
                                (Ov ov) universals
                        ) (Vector1.to_vector existentials) in
                        T.expose substitution concr_codo
                    | codomain -> codomain in

                let (_, substitution) = Vector.fold (fun (i, substitution) {T.name; _} ->
                    (i + 1, Name.Map.add name i substitution)
                ) (0, Name.Map.empty) universals in
                { TS.typ = T.Impli {universals = Vector.map (fun {T.kind; _} -> kind) universals
                     ; domain = T.close substitution domain
                     ; codomain = T.close substitution codomain }
                ; kind = T.aType }

            | TupleT typs ->
                let typings = Vector.map (elab env) typs in
                typings |> Vector.fold_right (fun {TS.typ = snd; kind = _} {TS.typ = fst; kind = _} ->
                    let fst_rep = repof_F ctrs typ.pos env fst in
                    let snd_rep = repof_F ctrs typ.pos env snd in
                    let rep = T.App {callee = App {callee = Prim PairRep; arg = fst_rep}; arg = snd_rep} in
                    {TS.typ = T.Pair {fst; snd}; kind = App {callee = Prim TypeIn; arg = rep} }
                ) {TS.typ = Prim Unit; kind = App {callee = Prim TypeIn; arg = Prim UnitRep}}

            | RecordT decls ->
                let {TS.typ = row; kind = _} = elab_row env typ.pos decls in
                {typ = Record row; kind = T.aType}

            | VariantT decls ->
                let {TS.typ = row; kind = _} = elab_row env typ.pos decls in
                {typ = Variant row; kind = T.aType}

            | RowT decls -> elab_row env typ.pos decls

            (*| AType.Singleton expr ->
                (match C.typeof env expr with
                | {term = _; typ; eff = Pure} -> (Hole, typ)
                | _ -> Env.reportError env typ.pos (ImpureType expr.v))*)

            | PrimT pt -> {typ = Prim pt; kind = kindof_prim pt}

            | Fn _ | ImpliFn _ | App _ | PrimApp _
            | Ann _
            | Tuple _ | Focus _ | Record _ | Select _
            | Var _ | Wild _ | Const _ ->
                let carrie =
                    let kind = T.Uv (Env.uv env false T.aType) in
                    T.Uv (Env.uv env false kind) in
                let {TS.term = _; eff} = Typing.check ctrs env (T.Proxy carrie) typ in
                ignore (Constraints.unify ctrs typ.pos env eff EmptyRow);
                let (_, carrie) = Env.reabstract env carrie in
                {typ = carrie; kind = kindof_F ctrs typ.pos env carrie}

        and elab_domain env (domain : AExpr.t) =
            let ((pat : FExpr.pat), env, _) =
                Typing.typeof_pat ctrs false false env Explicit domain in
            (pat.ptyp, env)

        and elab_row env pos decls =
            let row = Vector.fold_right (fun base -> function
                | ADecl.Decl (_, {v = Var label; _}, typ) ->
                    let {TS.typ = field; kind = _} = elab env typ in
                    T.With {base; label; field}
                | _ -> bug (Some pos) ~msg: "bad record type field reached typechecker"
            ) EmptyRow decls in
            {typ = row; kind = kindof_F ctrs pos env row}

        (*and analyze_decl env = function
            | ADecl.Decl (_, pat, typ) ->
                let (pat, env, vars) = Typing.typeof_pat ctrs false false env Explicit pat in
                (pat, env, vars, typ)

            | Def (_, pat, expr) ->
                let (pat, env, vars) = Typing.typeof_pat ctrs false false env Explicit pat in
                let expr' = AExpr.PrimApp (TypeOf, Vector.singleton expr) in
                (pat, env, vars, {expr with v = expr'})

            | Type typ -> todo (Some typ.pos)

        and elaborate_decl env (vars, lhs, rhs) decl =
            let span = ADecl.pos decl in
            if Vector.length vars > 0
            then Env.force_typ (fun env typ ->
                    let {TS.typ; kind} = elab env typ in
                    (typ, kind))
                (fun span env sub super -> ignore (Constraints.subtype ctrs span env sub super))
                env span (Vector.get vars 0).FExpr.name
            else begin
                let {TS.typ = rhs; kind = _} = elab env rhs in
                ignore (Constraints.subtype ctrs span env rhs lhs)
            end*)

        and check env kind ({Util.pos = span; _} as typ) =
            let {TS.typ; kind = kind'} = elab env typ in
            ignore (Constraints.unify ctrs span env kind' kind);
            typ in

        let (env, existentials) = Env.push_existential env in
        let {TS.typ; kind} = elab env typ in
        let typ : T.t = match Vector1.of_list !existentials with
            | Some existentials ->
                let (_, substitution) = Vector1.fold (fun (i, substitution) {T.name; _} ->
                    (i + 1, Name.Map.add name i substitution)
                ) (0, Name.Map.empty) existentials in
                Exists {existentials = existentials |> Vector1.map (fun {T.kind; _} -> kind)
                    ; body = T.close substitution typ}
            | None -> typ in
        {TS.typ; kind}

    let check ctrs env kind (({pos = span; _} as typ) : AExpr.t) =
        let {TS.typ; kind = kind'} = elaborate ctrs env typ in
        ignore (Constraints.unify ctrs span env kind' kind);
        typ

    let eval span _ typ =
        let (let*) = Option.bind in
        let (let+) = Fun.flip Option.map in

        let rec eval = function
            | T.App {callee; arg} ->
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
            | Ov _ (*ov as typ*) -> todo (Some span)
                (*(match Env.get_implementation env ov with
                | Some (axname, _, uv) ->
                    let typ = T.Uv uv in
                    let+ (typ, co) = eval typ in
                    ( typ
                    , match co with
                      | Some co -> Some (T.Trans (AUse axname, co))
                      | None -> Some (AUse axname) )
                | None -> Some (typ, None))*)
            | Uv uv as typ ->
                (match !uv with
                | Assigned typ -> eval typ (* OPTIMIZE: path compression *)
                | Unassigned (false, _, _, _) -> Some (typ, None)
                | Unassigned (true, _, _, _) -> None)
            | (Exists _ | Pi _ | Impli _ | Pair _ | Record _ | Variant _ | With _ | EmptyRow | Proxy _ | Prim _) as typ ->
                Some (typ, None)
            | Bv _ -> unreachable (Some span) ~msg: "`Bv` in `eval`"

        and apply callee arg = match callee with
            (* NOTE: Arg kinds do not need to be checked here because all `App`s originate from functors: *)
            | T.Fn _ -> todo (Some span) (*{param = _; body} -> eval (Env.expose env (Vector.singleton arg) body)*)
            | Ov _ | App _ | Prim _ -> Some (T.App {callee; arg}, None)
            | Uv uv ->
                (match !uv with
                | Unassigned _ -> None
                | Assigned _ -> unreachable (Some span) ~msg: "Assigned in `apply`.")
            | Exists _ | Pi _ | Impli _ | Pair _ | Record _ | Variant _ | With _ | EmptyRow | Proxy _ ->
                unreachable (Some span) ~msg: "uncallable type in `eval.apply`"
            | Bv _ -> unreachable (Some span) ~msg: "`Bv` in `eval.apply`"
        in eval typ
end

