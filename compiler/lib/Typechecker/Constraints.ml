open Asserts

module TS = TyperSigs
module T = FcType.Type
module E = Fc.Term.Expr
module Coercer = Fc.Term.Coercer
module Tx = Transactional
open Constraint
open Tx.Ref

module Make (K : TS.KINDING) = struct
    type queue = Constraint.queue

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

    (* FIXME: prevent nontermination from impredicative instantiation: *)
    let rec solve_subtype_whnf ctrs span env sub super =
        let (let+) = Fun.flip Option.map in

        match (sub, super) with
        | (T.Exists _, super) -> (match super with
            | Uv _ -> None
            | _ ->
                todo (Some span) ~msg: (Util.doc_to_string (T.to_doc sub) ^ " <: "
                ^ Util.doc_to_string (T.to_doc super)))

        | (sub, T.Impli {universals = _; domain = _; codomain = _}) -> (match sub with
            | Uv _ -> None
            | _ ->
                todo (Some span) ~msg: (Util.doc_to_string (T.to_doc sub) ^ " <: "
                ^ Util.doc_to_string (T.to_doc super)))

        | (sub, Pi {universals = super_universals; domain = _; eff = _; codomain = _})
          when Vector.length super_universals > 0 -> (match sub with
            | Uv _ -> None
            | _ ->
                todo (Some span) ~msg: (Util.doc_to_string (T.to_doc sub) ^ " <: "
                ^ Util.doc_to_string (T.to_doc super)))

        | (sub, Exists _) -> (match sub with
            | Uv _ -> None
            | _ ->
                todo (Some span) ~msg: (Util.doc_to_string (T.to_doc sub) ^ " <: "
                ^ Util.doc_to_string (T.to_doc super)))

        | (Impli {universals = _; domain = _; codomain = _}, super) -> (match super with
            | Uv _ -> None
            | _ ->
                todo (Some span) ~msg: (Util.doc_to_string (T.to_doc sub) ^ " <: "
                ^ Util.doc_to_string (T.to_doc super)))

        | (Pi {universals = sub_universals; domain = _; eff = _; codomain = _}, super)
          when Vector.length sub_universals > 0 -> (match super with
            | Uv _ -> None
            | _ ->
                todo (Some span) ~msg: (Util.doc_to_string (T.to_doc sub) ^ " <: "
                ^ Util.doc_to_string (T.to_doc super)))

        | (Pair {fst = sub_fst; snd = sub_snd}, super) -> (match super with
            | Uv _ -> None
            | Pair {fst = super_fst; snd = super_snd} -> (* covariant *)
                let fst_co = subtype ctrs span env sub_fst super_fst in
                let snd_co = subtype ctrs span env sub_snd super_snd in

                Some (match (fst_co, snd_co) with
                    | (Some fst_co, Some snd_co) -> Some (Coercer.coercer (fun expr ->
                        E.at span super
                            (E.pair (Coercer.apply fst_co expr) (Coercer.apply snd_co expr))))
                    | (Some fst_co, None) -> Some (Coercer.coercer (fun expr ->
                        E.at span super (E.pair (Coercer.apply fst_co expr) expr)))
                    | (None, Some snd_co) -> Some (Coercer.coercer (fun expr ->
                        E.at span super (E.pair expr (Coercer.apply snd_co expr))))
                    | (None, None) -> None)

            | _ ->
                Env.report_error env {v = Subtype (sub, super); pos = span};
                None)

        | (Uv _, _) | (_, Uv _)
        | (Pi _, _) | (Record _, _) | (Proxy _, _) | (App _, _)
        | (Bv _, _) | (Ov _, _) | (Prim _, _) ->
            (* Nothing to instantiate, delegate to unification: *)
            Some (let+ co = solve_unify_whnf ctrs span env sub super in
                  Coercer.coercer (fun v -> E.at span super (E.cast v co)))

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
            if Tx.Ref.eq luv ruv
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
                    unreachable (Some span) ~msg: "Assigned uv in `solve_unify_whnf`")
        | (Uv uv, typ') | (typ', Uv uv) ->
            (match !uv with
            | Unassigned (false, _, kind, level) ->
                check_uv_assignee span env uv level Int.max_int typ';
                ignore (unify ctrs span env (K.kindof_F ctrs span env typ') kind);
                uv := Assigned typ';
                None
            | Unassigned (true, _, _, _) ->
                unreachable (Some span) ~msg: "Forward declared uv in `solve_unify_whnf`"
            | Assigned _ -> unreachable (Some span) ~msg: "Assigned `typ` in `solve_unify_whnf`")

        | (Exists _, _) ->
            todo (Some span) ~msg: (Util.doc_to_string (T.to_doc ltyp) ^ " ~ "
            ^ Util.doc_to_string (T.to_doc rtyp))

        | (Impli _, _) ->
            todo (Some span) ~msg: (Util.doc_to_string (T.to_doc ltyp) ^ " ~ "
            ^ Util.doc_to_string (T.to_doc rtyp))

        | (Pi {universals = luniversals; domain = ldomain; eff = leff; codomain = lcodomain}, rtyp) ->
            (match rtyp with
            | Pi {universals = runiversals; domain = rdomain; eff = reff; codomain = rcodomain} ->
                if Vector.length luniversals = 0 && Vector.length runiversals = 0
                then begin
                    let domain_co = unify ctrs span env ldomain rdomain in
                    let eff_co = unify ctrs span env leff reff in
                    let codomain_co = unify ctrs span env lcodomain rcodomain in

                    match (domain_co, eff_co, codomain_co) with
                    | (None, None, None) -> None
                    | _ -> todo (Some span)
                end else todo (Some span)
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Pair {fst = lfst; snd = lsnd}, rtyp) -> (match rtyp with
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

        | (Record lrow, rtyp) -> (match rtyp with
            | Record rrow ->
                let+ row_co = unify ctrs span env lrow rrow in
                T.RecordCo row_co
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (With _, _) ->
            todo (Some span) ~msg: (Util.doc_to_string (T.to_doc ltyp) ^ " ~ "
            ^ Util.doc_to_string (T.to_doc rtyp))

        | (Proxy lcarrie, rtyp) -> (match rtyp with
            | Proxy rcarrie ->
                let+ carrie_co = unify ctrs span env lcarrie rcarrie in
                ProxyCo carrie_co
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (App {callee; arg}, rtyp) -> (match rtyp with
            | App {callee = callee'; arg = arg'} ->
                (* NOTE: Callees must already be in WHNF because of the Krivine-style `K.eval`: *)
                let callee_co = solve_unify_whnf ctrs span env callee callee' in
                let arg_co = unify ctrs span env arg arg' in
                (match (callee_co, arg_co) with
                | (Some callee_co, Some arg_co) -> Some (Comp (callee_co, Vector1.singleton arg_co))
                | (Some callee_co, None) -> Some (Comp (callee_co, Vector1.singleton (T.Refl arg')))
                | (None, Some arg_co) -> Some (Comp (Refl callee', Vector1.singleton arg_co))
                | (None, None) -> None)
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (EmptyRow, rtyp) -> (match rtyp with
            | EmptyRow -> None
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Ov lov, rtyp) -> (match rtyp with
            | Ov rov when T.ov_eq lov rov -> None
            | _ ->
                Env.report_error env {v = Unify (ltyp, rtyp); pos = span};
                None)

        | (Prim pt, rtyp) -> (match rtyp with
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
        let+ (rtyp, co'') = K.eval span env rtyp in
        let co' = solve_unify_whnf ctrs span env ltyp rtyp in
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
end

