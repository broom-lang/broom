open Streaming
open Asserts

open Constraint
module TS = TyperSigs
module T = FcType.Type
module E = Fc.Term.Expr
module Stmt = Fc.Term.Stmt
module Coercer = Fc.Term.Coercer
module Tx = Transactional
open Tx.Ref

module Make (K : TS.KINDING) = struct

(* # Solvers *)

    (* Occurs check, ov escape check, HKT capturability check and uv level updates.
       Complected for speed. *)
    let check_uv_assignee span env uv level max_uv_level typ =
        let rec check : T.t -> unit = function
            | Exists {existentials = _; body} -> check body
            | Pi {universals = _; domain; eff; codomain} -> check domain; check eff; check codomain
            | Impli {universals = _; domain; codomain} -> check domain; check codomain
            | Pair {fst; snd} -> check fst; check snd
            | Record row -> check row
            | With {base; label = _; field} -> check base; check field
            | EmptyRow -> ()
            | Proxy carrie -> check carrie
            | Fn {param = _; body} -> check body
            | App {callee; arg} -> check callee; check arg
            | Ov _ -> todo (Some span) (*((_, level') as ov) ->
                (match Env.get_implementation env ov with
                | Some (_, _, uv') -> check (Uv uv')
                | None ->
                    if level' <= level
                    then ()
                    else Env.reportError env pos (Escape ov))*)
            | Uv uv' ->
                (match !uv' with
                | Unassigned (is_fwd, name, kind, level') ->
                    if uv = uv'
                    then Env.report_error env {v = Occurs (uv, typ); pos = span}
                    else if level' <= level
                    then ()
                    else if level' <= max_uv_level
                    then uv' := (Unassigned (is_fwd, name, kind, level)) (* hoist *)
                    else Env.report_error env {v = IncompleteImpl (uv, uv'); pos = span}
                | Assigned typ -> check typ)
            | Bv _ | Prim _ -> () in
        check typ

    let rec eval_with_label ctrs span env typ label =
        let (let+) = Fun.flip Option.map in

        let rec eval_with_label typ =
            match K.eval span env typ with
            | Some (With {base; label = label'; field}, co) ->
                if Name.equal label' label
                then Some (base, field, co)
                else begin
                    let+ (base, field', base_co) = eval_with_label base in
                    ( T.With {base; label = label'; field}, field'
                    , match (co, base_co) with
                      | (Some co, Some base_co) ->
                          Some (T.Trans (co, WithCo {base = base_co; label; field = Refl field}))
                      | (Some _ as co, None) -> co
                      | (None, Some base_co) ->
                          Some (WithCo {base = base_co; label; field = Refl field})
                      | (None, None) -> None )
                end

            | Some (Uv uv, co) -> (* FIXME: 'scopedlabels' termination check: *)
                (match !uv with
                | Unassigned (false, _, kind, level) ->
                    let base = T.Uv (Env.uv env false T.aRow) in
                    let field = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
                    let typ' = T.With {base; label; field} in
                    check_uv_assignee span env uv level Int.max_int typ';
                    ignore (unify ctrs span env T.aRow kind);
                    uv := Assigned typ';
                    Some (base, field, co)

                | Unassigned (true, _, _, _) -> None
                | Assigned _ -> unreachable (Some span))

            | Some (typ, co) ->
                let base = T.Uv (Env.uv env false T.aRow) in
                let field = T.Uv (Env.uv env false (Env.some_type_kind env false)) in
                let typ' = T.With {base; label; field} in
                Env.report_error env {v = Unify (typ', typ); pos = span};
                Some (base, field, co)

            | None -> None in
        eval_with_label typ

    (* FIXME: prevent nontermination from impredicative instantiation: *)
    and solve_subtype_whnf ctrs span env sub super =
        let (let+) = Fun.flip Option.map in

        match (sub, super) with
        | (T.Exists {existentials; body}, super) -> (match super with
            | Uv _ -> None
            | super ->
                let (env, skolems, typ) = Env.push_abs_skolems env existentials body in
                let coerce = subtype ctrs span env typ super in
                let skolems = Vector1.map (fun {T.name; kind; _} -> (name, kind)) skolems in
                Some (match coerce with
                | Some coerce -> Some (Coercer.coercer (fun expr ->
                    let var = E.fresh_var Explicit typ in
                    let use = E.at span var.vtyp (E.use var) in
                    E.at span super (E.unpack skolems var expr (Coercer.apply coerce use))))
                | None -> Some (Coercer.coercer (fun expr ->
                    let var = E.fresh_var Explicit typ in
                    let use = E.at span var.vtyp (E.use var) in
                    E.at span super (E.unpack skolems var expr use)))))

        | (sub, T.Impli {universals; domain; codomain}) -> (match sub with
            | Uv _ -> None
            | sub ->
                let (env, skolems, domain, codomain) =
                    Env.push_impli_skolems env universals domain codomain in
                let param = E.fresh_var Implicit domain in
                let env = Env.push_val false env param in
                let coerce_codomain = subtype ctrs span env sub codomain in
                let universals = Vector.map (fun {T.name; kind; _} -> (name, kind)) skolems in
                Some (match coerce_codomain with
                    | Some coerce_codomain -> Some (Coercer.coercer (fun expr ->
                        let value = Coercer.apply coerce_codomain expr in
                        let var = E.fresh_var Explicit codomain in
                        let pat = E.pat_at span codomain (VarP var) in
                        let body = E.at span codomain (E.use var) in
                        E.at span super (E.let'
                            (Vector.singleton (Stmt.Def (span, pat, value)))
                            (E.at span super (E.fn universals param body)))))
                    | None -> Some (Coercer.coercer (fun expr ->
                        E.at span super (E.fn universals param expr)))))

        | (sub, Exists {existentials; body}) -> (match sub with
            | Uv _ -> None
            | sub ->
                let (uvs, super) = Env.instantiate_abs env existentials body in
                let coerce = subtype ctrs span env sub super in
                let existentials = Vector1.map (fun uv -> T.Uv uv) uvs |> Vector1.to_vector in
                Some (match coerce with
                | Some coerce -> Some (Coercer.coercer (fun expr ->
                    E.at span super (E.pack existentials (Coercer.apply coerce expr))))
                | None -> Some (Coercer.coercer (fun expr ->
                    E.at span super (E.pack existentials expr)))))

        | (Impli {universals; domain; codomain}, super) -> (match super with
            | Uv _ -> None
            | super ->
                let (uvs, domain, codomain) =
                    Env.instantiate_impli env universals domain codomain in
                let coerce_codomain = subtype ctrs span env codomain super in
                let arg = resolve ctrs span env domain in
                let uvs = Vector.map (fun uv -> T.Uv uv) uvs in
                Some (match coerce_codomain with
                | Some coerce_codomain -> Some (Coercer.coercer (fun expr ->
                    Coercer.apply coerce_codomain (E.at span super (E.app expr uvs arg))))
                | None -> Some (Coercer.coercer (fun expr ->
                    E.at span super (E.app expr uvs arg)))))

        | ( Pi {universals = sub_universals; domain = sub_domain; eff = sub_eff
                ; codomain = sub_codomain}
          , Pi {universals = super_universals; domain = super_domain; eff = super_eff
                ; codomain = super_codomain} )
          when Vector.length sub_universals > 0 || Vector.length super_universals > 0 ->
            let (env, super_universals, super_domain, super_eff, super_codomain) =
                Env.push_arrow_skolems env super_universals super_domain super_eff super_codomain in
            let (uvs, sub_domain, sub_eff, sub_codomain) =
                Env.instantiate_arrow env sub_universals sub_domain sub_eff sub_codomain in

            let coerce_domain = subtype ctrs span env super_domain sub_domain in
            (* TODO: row opening à la Koka: *)
            ignore (unify ctrs span env sub_eff super_eff);
            let coerce_codomain = subtype ctrs span env sub_codomain super_codomain in

            let sub_universals = Vector.map (fun uv -> T.Uv uv) uvs in
            let super_universals =
                Vector.map (fun {T.name; kind; _} -> (name, kind)) super_universals in
            Some (match (coerce_domain, coerce_codomain) with
            | (Some coerce_domain, Some coerce_codomain) -> Some (Coercer.coercer (fun expr ->
                let param = E.fresh_var Explicit super_domain in
                let arg = Coercer.apply coerce_domain (E.at span super_domain (E.use param)) in
                let body = E.at span sub_codomain (E.app expr sub_universals arg) in
                let body = Coercer.apply coerce_codomain body in
                E.at span super (E.fn super_universals param body)))
            | (Some coerce_domain, None) -> Some (Coercer.coercer (fun expr ->
                let param = E.fresh_var Explicit super_domain in
                let arg = Coercer.apply coerce_domain (E.at span super_domain (E.use param)) in
                let body = E.at span sub_codomain (E.app expr sub_universals arg) in
                E.at span super (E.fn super_universals param body)))
            | (None, Some coerce_codomain) -> Some (Coercer.coercer (fun expr ->
                let param = E.fresh_var Explicit super_domain in
                let arg = E.at span super_domain (E.use param) in
                let body = E.at span sub_codomain (E.app expr sub_universals arg) in
                let body = Coercer.apply coerce_codomain body in
                E.at span super (E.fn super_universals param body)))
            | (None, None) -> None)

        | ( (Pi {universals; domain = _; eff = _; codomain = _}, Uv _)
          | (Uv _, Pi {universals; domain = _; eff = _; codomain = _}) )
          when Vector.length universals > 0 -> None

        | (Uv _, _) | (_, Uv _)
        | (Pi _, _) | (Record _, _) | (Proxy _, _) | (App _, _)
        | (Bv _, _) | (Ov _, _) | (Prim _, _) ->
            (* Nothing to instantiate, delegate to unification: *)
            let+ co = solve_unify_whnf ctrs span env sub super in
            (match co with
            | Some co -> Some (Coercer.coercer (fun v -> E.at span super (E.cast v co)))
            | None -> None)

        | (Pair {fst = sub_fst; snd = sub_snd}, super) -> Some (match super with
            | Pair {fst = super_fst; snd = super_snd} -> (* covariant *)
                let fst_co = subtype ctrs span env sub_fst super_fst in
                let snd_co = subtype ctrs span env sub_snd super_snd in

                (match (fst_co, snd_co) with
                | (Some fst_co, Some snd_co) -> Some (Coercer.coercer (fun expr ->
                    E.at span super (E.pair
                        (Coercer.apply fst_co (E.at span sub_fst (E.fst expr)))
                        (Coercer.apply snd_co (E.at span sub_snd (E.snd expr))))))
                | (Some fst_co, None) -> Some (Coercer.coercer (fun expr ->
                    E.at span super (E.pair
                        (Coercer.apply fst_co (E.at span sub_fst (E.fst expr)))
                        (E.at span sub_snd (E.snd expr)))))
                | (None, Some snd_co) -> Some (Coercer.coercer (fun expr ->
                    E.at span super (E.pair
                        (E.at span sub_fst (E.fst expr))
                        (Coercer.apply snd_co (E.at span sub_snd (E.snd expr))))))
                | (None, None) -> None)

            | _ ->
                Env.report_error env {v = Subtype (sub, super); pos = span};
                None)

        (* TODO: Should these be outright unreachable?: *)
        | (With _, super) ->
            ignore (solve_unify_whnf ctrs span env sub super);
            Some (Some (Coercer.coercer (fun _ -> bug (Some span) ~msg: "With coercion called")))
        | (EmptyRow, super) ->
            ignore (solve_unify_whnf ctrs span env sub super);
            Some (Some (Coercer.coercer (fun _ -> bug (Some span) ~msg: "EmptyRow coercion called")))
        | (Fn _, super) ->
            ignore (solve_unify_whnf ctrs span env sub super);
            Some (Some (Coercer.coercer (fun _ -> bug (Some span) ~msg: "Fn coercion called")))

    and solve_subtype ctrs span env sub super =
        let (let*) = Option.bind in
        let (let+) = Fun.flip Option.map in

        let* (sub, co) = K.eval span env sub in
        let* (super, co') = K.eval span env super in
        let+ coerce = solve_subtype_whnf ctrs span env sub super in
        (match (co, coerce, co') with
        | (Some co, Some coerce, Some co') -> Some (Coercer.coercer (fun v ->
            let castee = Coercer.apply coerce (E.at span sub (E.cast v co)) in
            E.at span super (E.cast castee (Symm co'))))
        | (Some co, Some coerce, None) -> Some (Coercer.coercer (fun v ->
            Coercer.apply coerce (E.at span sub (E.cast v co))))
        | (Some co, None, Some co') -> Some (Coercer.coercer (fun v ->
            E.at span super (E.cast v (Trans (co, Symm co')))))
        | (Some co, None, None) -> Some (Coercer.coercer (fun v ->
            E.at span super (E.cast v co)))
        | (None, Some coerce, Some co') -> Some (Coercer.coercer (fun v ->
            E.at span super (E.cast (Coercer.apply coerce v) (Symm co'))))
        | (None, Some coerce, None) -> Some coerce
        | (None, None, Some co') -> Some (Coercer.coercer (fun v ->
            E.at span super (E.cast v co')))
        | (None, None, None) -> None)

    and solve_unify_whnf ctrs span env ltyp rtyp =
        let (let+) = Fun.flip Option.map in

        match (ltyp, rtyp) with
        | (T.Uv luv, T.Uv ruv) ->
            Some (if Tx.Ref.eq luv ruv
                then None
                else (match (!luv, !ruv) with (* OPTIMIZE: Union-Find ranking: *)
                    | (Unassigned (false, _, lkind, llevel), Unassigned (false, _, rkind, rlevel)) ->
                        ignore (unify ctrs span env lkind rkind);
                        if rlevel < llevel
                        then luv := Assigned rtyp
                        else ruv := Assigned ltyp;
                        None
                    | (Unassigned (true, _, _, _), _) | (_, Unassigned (true, _, _, _)) ->
                        unreachable (Some span) ~msg: "Forward declared uv in `solve_unify_whnf`"
                    | (Assigned _, _) | (_, Assigned _) ->
                        unreachable (Some span) ~msg: "Assigned uv in `solve_unify_whnf`"))
        | (Uv uv, typ') | (typ', Uv uv) ->
            Some (match !uv with
                | Unassigned (false, _, kind, level) ->
                    check_uv_assignee span env uv level Int.max_int typ';
                    ignore (unify ctrs span env (K.kindof_F ctrs span env typ') kind);
                    uv := Assigned typ';
                    None
                | Unassigned (true, _, _, _) ->
                    unreachable (Some span) ~msg: "Forward declared uv in `solve_unify_whnf`"
                | Assigned _ -> unreachable (Some span) ~msg: "Assigned `typ` in `solve_unify_whnf`")

        | (Exists {existentials = lexistentials; body = lbody}, rtyp) ->
            Some (match rtyp with
            | Exists {existentials = rexistentials; body = rbody} ->
                let (env, skolems, lbody) = Env.push_abs_skolems env lexistentials lbody in
                let (uvs, rbody) = Env.instantiate_abs env rexistentials rbody in

                let body_co = unify ctrs span env lbody rbody in

                (let seen = T.OvHashSet.create 0 in
                uvs |> Vector1.iter (fun uv -> match !uv with
                    | T.Assigned (Ov ov) when Vector1.exists ((=) ov) skolems ->
                        if not (T.OvHashSet.mem seen ov)
                        then T.OvHashSet.insert seen ov
                        else failwith ("insufficiently abstract rhs at " ^ Util.span_to_string span)
                    | Assigned _ -> failwith ("insufficiently abstract lhs at " ^ Util.span_to_string span)
                    | Unassigned _ -> ()
                ));

                let subst = Vector1.foldi (fun subst i {T.name; _} ->
                    Name.Map.add name i subst
                ) Name.Map.empty skolems in
                let body_co : T.t T.coercion = match body_co with
                    | Some body_co -> T.close_coercion subst body_co
                    | None -> Refl rbody in
                Some (ExistsCo (rexistentials, body_co))

            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Impli {universals = luniversals; domain = ldomain; codomain = lcodomain}, _) ->
            Some (match rtyp with
            | Impli {universals = runiversals; domain = rdomain; codomain = rcodomain} ->
                let (env, skolems, rdomain, rcodomain) =
                    Env.push_impli_skolems env runiversals rdomain rcodomain in
                let (uvs, ldomain, lcodomain) =
                    Env.instantiate_impli env luniversals ldomain lcodomain in

                let domain_co = unify ctrs span env rdomain ldomain in
                let codomain_co = unify ctrs span env lcodomain rcodomain in

                (let seen = T.OvHashSet.create 0 in
                uvs |> Vector.iter (fun uv -> match !uv with
                    | T.Assigned (Ov ov) when Vector.exists ((=) ov) skolems ->
                        if not (T.OvHashSet.mem seen ov)
                        then T.OvHashSet.insert seen ov
                        else failwith ("insufficiently polymorphic lhs at " ^ Util.span_to_string span)
                    | Assigned _ -> failwith ("insufficiently polymorphic rhs at " ^ Util.span_to_string span)
                    | Unassigned _ -> ()
                ));

                let subst = Vector.foldi (fun subst i {T.name; _} ->
                    Name.Map.add name i subst
                ) Name.Map.empty skolems in
                Some (PiCo {universals = runiversals
                    ; domain = (match domain_co with
                        | Some domain_co -> T.close_coercion subst domain_co
                        | None -> Refl rdomain)
                    ; codomain = (match codomain_co with
                        | Some codomain_co -> T.close_coercion subst codomain_co
                        | None -> Refl rdomain)})

            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Pi {universals = luniversals; domain = ldomain; eff = leff; codomain = lcodomain}, rtyp) ->
            Some (match rtyp with
            | Pi {universals = runiversals; domain = rdomain; eff = reff; codomain = rcodomain} ->
                let (env, skolems, rdomain, reff, rcodomain) =
                    Env.push_arrow_skolems env runiversals rdomain reff rcodomain in
                let (uvs, ldomain, leff, lcodomain) =
                    Env.instantiate_arrow env luniversals ldomain leff lcodomain in

                let domain_co = unify ctrs span env rdomain ldomain in
                let _ = unify ctrs span env leff reff in
                let codomain_co = unify ctrs span env lcodomain rcodomain in

                (let seen = T.OvHashSet.create 0 in
                uvs |> Vector.iter (fun uv -> match !uv with
                    | T.Assigned (Ov ov) when Vector.exists ((=) ov) skolems ->
                        if not (T.OvHashSet.mem seen ov)
                        then T.OvHashSet.insert seen ov
                        else failwith ("insufficiently polymorphic lhs at " ^ Util.span_to_string span)
                    | Assigned _ -> failwith ("insufficiently polymorphic rhs at " ^ Util.span_to_string span)
                    | Unassigned _ -> ()
                ));

                let subst = Vector.foldi (fun subst i {T.name; _} ->
                    Name.Map.add name i subst
                ) Name.Map.empty skolems in
                Some (PiCo {universals = runiversals
                    ; domain = (match domain_co with
                        | Some domain_co -> T.close_coercion subst domain_co
                        | None -> Refl rdomain)
                    ; codomain = (match codomain_co with
                        | Some codomain_co -> T.close_coercion subst codomain_co
                        | None -> Refl rdomain)})

            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Pair {fst = lfst; snd = lsnd}, rtyp) -> Some (match rtyp with
            | Pair {fst = rfst; snd = rsnd} ->
                let fst_co = unify ctrs span env lfst rfst in
                let snd_co = unify ctrs span env lsnd rsnd in

                (match (fst_co, snd_co) with
                | (Some fst_co, Some snd_co) -> Some (PairCo (fst_co, snd_co))
                | (Some fst_co, None) -> Some (PairCo (fst_co, Refl rsnd))
                | (None, Some snd_co) -> Some (PairCo (Refl rfst, snd_co))
                | (None, None) -> None)

            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Record lrow, rtyp) -> Some (match rtyp with
            | Record rrow ->
                let+ row_co = unify ctrs span env lrow rrow in
                T.RecordCo row_co
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (With {base = lbase; label = llabel; field = lfield}, rtyp) -> (match rtyp with
            | With {base = rbase; label = rlabel; field = rfield} ->
                (if Name.equal llabel rlabel
                then Some (lbase, lfield, None)
                else begin
                    eval_with_label ctrs span env lbase rlabel
                    |> Option.map (fun (lbase', lfield', base_co) ->
                        ( T.With {base = lbase'; label = llabel; field = lfield}, lfield'
                        , match base_co with
                          | Some base_co ->
                              Some (T.WithCo {base = base_co; label = llabel; field = Refl lfield})
                          | None -> None ))
                end)
                |> Option.map (fun (lbase, lfield, lco) ->

                    let base_co = unify ctrs span env lbase rbase in
                    let field_co = unify ctrs span env lfield rfield in

                    (match (lco, base_co, field_co) with
                    | (Some lco, Some base_co, Some field_co) ->
                        Some (T.Trans (lco, WithCo {base = base_co; label = rlabel; field = field_co}))
                    | (Some lco, Some base_co, None) ->
                        Some (T.Trans (lco, WithCo {base = base_co; label = rlabel; field = Refl rfield}))
                    | (Some lco, None, Some field_co) ->
                        Some (T.Trans (lco, WithCo {base = Refl rbase; label = rlabel; field = field_co}))
                    | (Some _ as lco, None, None) -> lco
                    | (None, Some base_co, Some field_co) ->
                        Some (WithCo {base = base_co; label = rlabel; field = field_co})
                    | (None, Some base_co, None) ->
                        Some (WithCo {base = base_co; label = rlabel; field = Refl rfield})
                    | (None, None, Some field_co) ->
                        Some (WithCo {base = Refl rbase; label = rlabel; field = field_co})
                    | (None, None, None) -> None))

            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                Some None)

        | (Proxy lcarrie, rtyp) -> Some (match rtyp with
            | Proxy rcarrie ->
                let+ carrie_co = unify ctrs span env lcarrie rcarrie in
                ProxyCo carrie_co
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (App {callee; arg}, rtyp) -> (match rtyp with
            | App {callee = callee'; arg = arg'} ->
                (* NOTE: Callees must already be in WHNF because of the Krivine-style `K.eval`: *)
                solve_unify_whnf ctrs span env callee callee' |> Option.map (fun callee_co ->
                    let arg_co = unify ctrs span env arg arg' in
                    (match (callee_co, arg_co) with
                    | (Some callee_co, Some arg_co) -> Some (T.Comp (callee_co, Vector1.singleton arg_co))
                    | (Some callee_co, None) -> Some (Comp (callee_co, Vector1.singleton (T.Refl arg')))
                    | (None, Some arg_co) -> Some (Comp (Refl callee', Vector1.singleton arg_co))
                    | (None, None) -> None))

            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                Some None)

        | (EmptyRow, rtyp) -> Some (match rtyp with
            | EmptyRow -> None
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Ov lov, rtyp) -> Some (match rtyp with
            | Ov rov when T.ov_eq lov rov -> None
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Prim pt, rtyp) -> Some (match rtyp with
            | Prim pt' when Prim.eq pt pt'-> None
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Fn _, _) -> unreachable (Some span) ~msg: "Fn in `solve_unify_whnf`"
        | (Bv _, _) -> unreachable (Some span) ~msg: "Bv in `solve_unify_whnf`"

    and solve_unify ctrs span env ltyp rtyp =
        let (let*) = Option.bind in
        let (let+) = Fun.flip Option.map in

        let* (ltyp, co) = K.eval span env ltyp in
        let* (rtyp, co'') = K.eval span env rtyp in
        let+ co' = solve_unify_whnf ctrs span env ltyp rtyp in
        match (co, co', co'') with
        | (Some co, Some co', Some co'') -> Some (T.Trans (Trans (co, co'), Symm co''))
        | (Some co, Some co', None) -> Some (Trans (co, co'))
        | (Some co, None, Some co'') -> Some (Trans (co, Symm co''))
        | (Some co, None, None) -> Some co
        | (None, Some co', Some co'') -> Some (Trans (co', Symm co''))
        | (None, Some co', None) -> Some co'
        | (None, None, Some co'') -> Some (Symm co'')
        | (None, None, None) -> None

    and solve ctrs =
        let solve1 = function
            | Subtype {span; env; sub; super; coerce} as ctr ->
                (match solve_subtype ctrs span env sub super with
                | Some co -> coerce := (match co with
                    | Some co -> co
                    | None -> Coercer.id)
                | None -> Tx.Queue.push ctrs ctr)

            | Unify {span; env; ltyp; rtyp; coercion} as ctr ->
                (match solve_unify ctrs span env ltyp rtyp with
                | Some co -> coercion := (match co with
                    | Some co -> co
                    | None -> Refl rtyp)
                | None -> Tx.Queue.push ctrs ctr) in

        (* FIXME: Ensure termination: *)
        let rec loop () =
            match Tx.Queue.pop ctrs with
            | Some ctr ->
                solve1 ctr;
                loop ()
            | None -> () in
        loop ()

(* # Generators *)

    and unify ctrs span env ltyp rtyp =
        match solve_unify ctrs span env ltyp rtyp with
        | Some co -> co
        | None ->
            let coercion = Tx.Ref.ref (T.Refl rtyp) in
            Tx.Queue.push ctrs (Unify {span; env; ltyp; rtyp; coercion});
            Some (T.Patchable coercion)

    (* OPTIMIZE: First try to subtype on the fly: *)
    and subtype ctrs span env sub super =
        match solve_subtype ctrs span env sub super with
        | Some co -> co
        | None ->
            let coerce = Tx.Ref.ref Coercer.id in
            Tx.Queue.push ctrs (Subtype {span; env; sub; super; coerce});
            Some (Coercer.coercer (fun expr -> E.at span super (E.convert coerce expr)))

    and resolve ctrs span env super =
        let results = Env.implicits env
            |> Stream.map (fun ({E.vtyp; name = _; plicity = _} as var) ->
                Tx.transaction (fun () ->
                    let errors = ref [] in
                    let coerce =
                        let env = Env.with_error_handler Env.empty
                            (fun error -> errors := error :: !errors) in
                        subtype ctrs span env vtyp super in
                    match !errors with
                    | [] -> Some (var, coerce)
                    | _ :: _ -> None))
            |> Stream.flat_map (fun ores -> ores |> Option.to_seq |> Source.seq |> Stream.from)
            |> Stream.into (Vector.sink ()) in
        match Vector.length results with
        | 1 ->
            let (var, coercion) = Vector.get results 0 in
            Coercer.apply_opt coercion (E.at span var.E.vtyp (E.use var))

        | 0 -> todo (Some span) ~msg: "resolution did not find"
        | _ -> todo (Some span) ~msg: "ambiguous resolution"
end

