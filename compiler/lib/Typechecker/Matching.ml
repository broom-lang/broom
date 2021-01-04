open Streaming
open Asserts

module ResidualMonoid = struct
    include Monoid.OfSemigroup(Residual)

    let skolemized skolems m = match Vector1.of_vector skolems with
        | Some skolems -> Option.map (fun r -> Residual.Skolems (skolems, r)) m
        | None -> m
end

module Make
    (Env : TyperSigs.ENV)
    (K : TyperSigs.KINDING with type env = Env.t)
: TyperSigs.MATCHING with type env = Env.t
= struct

module T = Fc.Type
module E = Fc.Term.Expr
module Err = TypeError

type env = Env.t
type span = Util.span

type 'a matching = {coercion : 'a; residual : Residual.t option}

let ref = TxRef.ref
let (!) = TxRef.(!)
let sibling = Env.sibling

let trans_with =
    let (let*) = Option.bind in
    let (let+) = Fun.flip Option.map in
fun co base label field ->
    let* co = co in
    let+ base = base in
    T.Trans (co, WithCo {base; label; field = Refl field})

(* Massage `typ` into a `With`, returning `(coercion, base, field_t)`: *)
let pull_row pos env label' typ : T.coercion option * T.t * T.t =
    let rec pull typ = match K.eval pos env typ with
        | Some (With {base; label; field}, co) when label = label' -> (co, base, field)
        | Some (With {base; label; field}, co) ->
            let (base_co, base, field'') = pull base in
            ( trans_with co base_co label field
            , T.With {base; label; field}, field'' )
        | Some (Uv uv, co) -> (* FIXME: 'scopedlabels' termination check: *)
            let base = T.Uv (sibling env T.aRow uv) in
            let field = T.Uv (sibling env T.aRow uv) in
            Env.set_uv env pos uv (Assigned (With {base; label = label'; field}));
            (co, base, field)
        | Some _ ->
            let template = T.WithL {base = Hole; label = label'; field = Hole} in
            Env.reportError env pos (Unusable (template, typ));
            (None, Uv (Env.uv env T.aRow), Uv (Env.uv env T.aType))
        | None -> todo (Some pos) ~msg: "pull_row None" in
    pull typ

let match_rows : Util.span -> Env.t -> T.t -> T.t -> Name.t CCVector.ro_vector
    * T.coercion option * T.t * T.t CCVector.ro_vector
    * T.t * T.t CCVector.ro_vector * T.coercion option
= fun pos env row row' ->
    let labels = CCVector.create () in
    let fields = CCVector.create () in
    let fields' = CCVector.create () in
    let rec matchem row row' = match K.eval pos env row' with
        | Some (With {base = base'; label = label'; field = field'}, co') ->
            (* OPTIMIZE: computing `co` n times is probably redundant: *)
            let (co, base, field) = pull_row pos env label' row in
            let (base_co, base, base', base_co') = matchem base base' in (* OPTIMIZE: nontail *)
            CCVector.push labels label';
            CCVector.push fields field;
            CCVector.push fields' field';
            ( trans_with co base_co label' field, base
            , base', trans_with co' base_co' label' field' )
        | Some (base', co') -> (None, row, base', co')
        | None -> todo (Some pos) ~msg: "match_rows None" in
    let (co, base, base', co') = matchem row row' in
    ( CCVector.freeze labels
    , co, base, CCVector.freeze fields
    , base', CCVector.freeze fields', Option.map (fun co' -> T.Symm co') co')

(* # Focalization *)

let focalize : span -> Env.t -> T.t -> T.template -> Coercer.t option * T.t
= fun pos env typ template ->
    let articulate_template uv_typ template = match uv_typ with
        | T.Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                let (uv, typ) = match template with
                    | T.TupleL _ -> failwith "cannot articulate tuple; width unknown"
                    | PiL _ ->
                        let dkind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
                        let cdkind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
                        (uv, T.Pi { universals = Vector.of_list []
                                ; domain = T.Uv (sibling env dkind uv)
                                ; eff = Uv (sibling env T.aRow uv)
                                ; codomain = Uv (sibling env cdkind uv) })
                    | ProxyL _ ->
                        let kind = T.Uv (sibling env T.aKind uv) in
                        (uv, Proxy (Uv (sibling env kind uv)))
                    | WithL {base = _; label; field = _} ->
                        (uv, (With {base = Uv (sibling env T.aRow uv)
                            ; label; field = Uv (sibling env T.aType uv)}))
                    | Hole -> unreachable (Some pos) ~msg: "Hole as template in `articulate_template`" in
                Env.set_uv env pos uv (Assigned typ);
                typ
            | Assigned _ -> unreachable (Some pos) ~msg: "`articulate_template` on assigned uv")
        | _ -> unreachable (Some pos) ~msg: "`articulate_template` on non-uv" in

    let focalize_whnf typ = match typ with
        | T.Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ -> (None, articulate_template typ template)
            | Assigned _ -> unreachable (Some pos) ~msg: "Assigned uv in `focalize`.")
        | Impli _ -> todo (Some pos)
        | _ ->
            (match template with
            | TupleL min_length ->
                (match typ with
                | Tuple typs when Vector.length typs >= min_length -> (None, typ)
                | _ ->
                    Env.reportError env pos (Unusable (template, typ));
                    let typ : T.t = Uv (Env.uv env T.aType) in
                    (None, articulate_template typ template))
            | PiL _ -> (* TODO: arity check (or to `typeof`/`App`?) *)
                (match typ with
                | Pi _ -> (None, typ)
                | _ ->
                    Env.reportError env pos (Unusable (template, typ));
                    let typ : T.t = Uv (Env.uv env T.aType) in
                    (None, articulate_template typ template))
            | ProxyL _ ->
                (match typ with
                | Proxy _ -> (None, typ)
                | _ ->
                    let typ : T.t = Uv (Env.uv env T.aType) in
                    (None, articulate_template typ template))
            | WithL {base = _; label; field = _} ->
                let (co, base, field) = pull_row pos env label typ in
                let coerce = co |> Option.map (fun co -> Coercer.coercer (fun castee ->
                    E.at pos (With {base; label; field}) (E.cast castee co))) in
                (coerce, With {base; label; field})
            | Hole -> unreachable (Some pos) ~msg: "Hole as template in `focalize`.") in

    match K.eval pos env typ with
    | Some (typ', coercion) ->
        let (coerce, typ) = focalize_whnf typ' in
        let coerce = match (coercion, coerce) with
          | (Some coercion, Some coerce) -> Some (Coercer.coercer (fun castee ->
                Coercer.apply coerce (E.at pos typ' (E.cast castee coercion))))
          | (Some coercion, None) -> Some (Coercer.coercer (fun castee ->
                E.at pos typ' (E.cast castee coercion)))
          | (None, Some _) -> coerce
          | (None, None) -> None in
        (coerce, typ)
    | None -> unreachable (Some pos) ~msg: "`whnf` failed in `focalize`."

(* # Subtyping *)

let rec subtype : span -> bool -> Env.t -> T.t -> T.t -> Coercer.t option matching
= fun pos occ env typ super ->
    let empty = ResidualMonoid.empty in
    let combine = ResidualMonoid.combine in

    let articulate pos env uv_typ template = match uv_typ with
        | T.Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned (_, _, level) -> (* FIXME: use uv kind *)
                let (uv, typ) = match template with
                    | T.Uv uv' ->
                        (match Env.get_uv env uv' with
                        | Unassigned (_, _, level') -> (* FIXME: use uv kind *)
                            if level' <= level
                            then (uv, template)
                            else (uv', uv_typ)
                        | Assigned _ -> unreachable (Some pos) ~msg: "Assigned as template of `articulate`")

                    | Ov ((_, level') as ov) ->
                        if level' <= level
                        then ()
                        else Env.reportError env pos (Escape ov);
                        (uv, Ov ov)

                    | PromotedArray typs -> (match Vector1.of_vector typs with
                        | Some typs1 ->
                            let kind = K.kindof_F pos env (Vector1.get typs1 0) in
                            (uv, PromotedArray (Vector.map (fun _ -> T.Uv (sibling env kind uv)) typs))
                        | None -> (uv, PromotedArray Vector.empty))
                    | PromotedTuple typs ->
                        (uv, PromotedTuple (Vector.map (fun typ ->
                            T.Uv (sibling env (K.kindof_F pos env typ) uv)
                        ) typs))
                    | Tuple typs ->
                        (uv, Tuple (Vector.map (fun typ ->
                            T.Uv (sibling env (K.kindof_F pos env typ) uv)
                        ) typs))
                    | Pi _ ->
                        let dkind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
                        let cdkind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
                        (uv, Pi { universals = Vector.empty
                                ; domain = T.Uv (sibling env dkind uv)
                                ; eff = Uv (sibling env T.aRow uv)
                                ; codomain = Uv (sibling env cdkind uv) })
                    | Impli _ ->
                        let dkind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
                        let cdkind = T.App (Prim TypeIn, Uv (Env.uv env T.rep)) in
                        (uv, Impli { universals = Vector.empty
                                ; domain = T.Uv (sibling env dkind uv)
                                ; codomain = Uv (sibling env cdkind uv) })
                    | Record _ -> (uv, Record (Uv (sibling env T.aRow uv)))
                    | With {base = _; label; field = _} ->
                        (uv, With { base = Uv (sibling env T.aRow uv)
                            ; label; field = Uv (sibling env T.aType uv) })
                    | EmptyRow -> (uv, EmptyRow)
                    | Proxy _ ->
                        let kind : T.kind = Uv (sibling env T.aKind uv) in
                        (uv, Proxy (Uv (sibling env kind uv)))
                    | App (callee, arg) ->
                        ( uv, T.App (Uv (sibling env (K.kindof_F pos env callee) uv)
                            , Uv (sibling env (K.kindof_F pos env arg) uv)) )
                    | Prim pt -> (uv, Prim pt)

                    | Exists _ -> unreachable (Some pos) ~msg: "`Exists` as template of `articulate`"
                    | Fn _ -> unreachable (Some pos) ~msg: "`Fn` as template of `articulate`"
                    | Bv _ -> unreachable (Some pos) ~msg: "`Bv` as template of `articulate`" in
                Env.set_uv env pos uv (Assigned typ);
                typ
            | Assigned _ -> unreachable (Some pos) ~msg: "`articulate` on assigned uv")
        | _ -> unreachable (Some pos) ~msg: "`articulate` on non-uv" in

    let subtype_whnf : bool -> T.t -> T.t -> Coercer.t option matching
    = fun occ typ super -> match (typ, super) with
        (* TODO: uv impredicativity clashes *)
        | (Uv uv, Uv uv') when uv = uv' -> {coercion = None; residual = None}
        | (Uv uv, _) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                if occ then occurs_check pos env uv super else ();
                subtype pos false env (articulate pos env typ super) super
            | Assigned _ -> unreachable (Some pos) ~msg: "Assigned `typ` in `subtype_whnf`")
        | (_, Uv uv) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                if occ then occurs_check pos env uv typ else ();
                subtype pos false env typ (articulate pos env super typ)
            | Assigned _ -> unreachable (Some pos) ~msg: "Assigned `super` in `subtype_whnf`")

        | (Impli _, _) | (_, Impli _) -> todo (Some pos)

        | (Exists (existentials, body), _) ->
            let (env, skolems, typ) = Env.push_abs_skolems env existentials body in
            let {coercion = coerce; residual} = subtype pos occ env typ super in
            let skolems = Vector1.map fst skolems in
            { coercion = Some (Coercer.coercer (match coerce with
                | Some coerce -> (fun expr ->
                    let var = E.fresh_var typ in
                    let use = E.at pos var.vtyp (E.use var) in
                    E.at pos super (E.unpack skolems var expr (Coercer.apply coerce use)))
                | None -> (fun expr ->
                    let var = E.fresh_var typ in
                    let use = E.at pos var.vtyp (E.use var) in
                    E.at pos super (E.unpack skolems var expr use))))
            ; residual = ResidualMonoid.skolemized (Vector.map snd (Vector1.to_vector skolems))
                residual }
        | (_, Exists (existentials', body')) ->
            let (uvs, super) = Env.instantiate_abs env existentials' body' in
            let {coercion = coerce; residual} = subtype pos occ env typ super in
            let existentials = Vector1.map (fun uv -> T.Uv uv) uvs |> Vector1.to_vector in
            { coercion = Some (Coercer.coercer (match coerce with
                | Some coerce -> (fun expr ->
                    E.at pos super (E.pack existentials (Coercer.apply coerce expr)))
                | None -> (fun expr -> E.at pos super (E.pack existentials expr))))
            ; residual }

        | (PromotedArray _, _) -> (match super with
            | PromotedArray _ ->
                let {coercion = _; residual} = unify pos env typ super in
                { coercion = Some (Coercer.coercer (fun _ ->
                    bug (Some pos) ~msg: "PromotedArray coercion called"))
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (PromotedTuple _, _) -> (match super with
            | PromotedTuple _ ->
                let {coercion = _; residual} = unify pos env typ super in
                { coercion = Some (Coercer.coercer (fun _ ->
                    bug (Some pos) ~msg: "PromotedTuple coercion called"))
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (Tuple typs, _) -> (match super with
            | Tuple super_typs ->
                if Vector.length typs = Vector.length super_typs then begin
                    let coercions = CCVector.create () in
                    let (residual, noop) = Vector.fold2 (fun (residual, noop) typ super ->
                        let {coercion = coerce; residual = residual'} =
                            subtype pos occ env typ super in
                        CCVector.push coercions (typ, Option.value ~default: Coercer.id coerce);
                        (combine residual residual', noop && Option.is_none coerce)
                    ) (empty, true) typs super_typs in
                    let coercion = if not noop
                        then Some (Coercer.coercer (fun expr ->
                            let var = E.fresh_var typ in
                            let body = E.at pos super (E.values (coercions |> CCVector.mapi (fun i (typ, coerce) ->
                                let use = E.at pos typ (E.use var) in
                                Coercer.apply coerce (E.at pos typ (E.focus use i))
                            ) |> CCVector.to_array)) in
                            E.at pos super (E.let' [|Def (pos, var, expr)|] body)))
                        else None in
                    {coercion; residual}
                end else failwith "<: tuple lengths"
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        (* FIXME: forall <: uv impredicativity clash (?) *)
        | (Pi {universals; domain; eff; codomain}, _) -> (match super with
            | Pi { universals = universals'; domain = domain'; eff = eff'; codomain = codomain'} ->
                let (env, universals', domain', eff', codomain') =
                    Env.push_arrow_skolems env universals' domain' eff' codomain' in
                let (uvs, domain, eff, codomain) =
                    Env.instantiate_arrow env universals domain eff codomain in
                let {coercion = coerce_domain; residual = residual} =
                    subtype pos occ env domain' domain in
                (* TODO: row opening à la Koka: *)
                let {coercion = _; residual = eff_residual} = unify pos env eff eff' in
                let residual = combine residual eff_residual in
                let {coercion = coerce_codomain; residual = codomain_residual} =
                    subtype pos occ env codomain codomain' in
                let residual = combine residual codomain_residual in

                let universals = Vector.map (fun uv -> T.Uv uv) uvs in
                let universals' = Vector.map fst universals' in
                let coercion = match (coerce_domain, coerce_codomain) with
                    | (Some coerce_domain, Some coerce_codomain) -> Some (Coercer.coercer (fun expr ->
                        let param = E.fresh_var domain' in
                        let arg = Coercer.apply coerce_domain (E.at pos domain' (E.use param)) in
                        let body = E.at pos codomain (E.app expr universals arg) in
                        let body = Coercer.apply coerce_codomain body in
                        E.at pos super (E.fn universals' param body)))
                    | (Some coerce_domain, None) -> Some (Coercer.coercer (fun expr ->
                        let param = E.fresh_var domain' in
                        let arg = Coercer.apply coerce_domain (E.at pos domain' (E.use param)) in
                        let body = E.at pos codomain (E.app expr universals arg) in
                        E.at pos super (E.fn universals' param body)))
                    | (None, Some coerce_codomain) -> Some (Coercer.coercer (fun expr ->
                        let param = E.fresh_var domain' in
                        let arg = E.at pos domain' (E.use param) in
                        let body = E.at pos codomain (E.app expr universals arg) in
                        let body = Coercer.apply coerce_codomain body in
                        E.at pos super (E.fn universals' param body)))
                    | (None, None) -> None in
                {coercion; residual = ResidualMonoid.skolemized (Vector.map snd universals') residual}
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (Record row, _) -> (match super with
            | Record super_row ->
                let (labels, co, base, fields, super_base, super_fields, super_co) =
                    match_rows pos env row super_row in

                let fields_len = CCVector.length labels in
                let {coercion = _; residual} = subtype pos occ env base super_base in
                let field_cos = CCVector.create_with ~capacity: fields_len None in
                let (residual, noop_fieldcos) =
                    let rec loop residual noop_fieldcos i =
                        if i < fields_len
                        then begin
                            let {coercion = field_co; residual = residual'} =
                                subtype pos occ env (CCVector.get fields i) (CCVector.get super_fields i) in
                            CCVector.push field_cos field_co;
                            loop (combine residual residual') (noop_fieldcos && Option.is_none field_co)
                                (i + 1)
                        end else (residual, noop_fieldcos) in
                    loop residual true 0 in

                let coerce =
                    if not noop_fieldcos
                    then match super_base with
                        | EmptyRow -> Some (Coercer.coercer (fun expr ->
                            let var = E.fresh_var typ in
                            let field i =
                                let selectee = E.at pos typ (E.use var) in
                                let label = CCVector.get labels i in
                                let coerce = CCVector.get field_cos i |> Option.value ~default: Coercer.id in
                                let super = CCVector.get super_fields i in
                                let selection = E.at pos super (E.select selectee label) in
                                (label, Coercer.apply coerce selection) in
                            let body = E.at pos super (E.record (Array.init fields_len field)) in
                            E.at pos super (E.let' [|Def (pos, var, expr)|] body)))
                        | _ -> Some (Coercer.coercer (fun expr ->
                            let var = E.fresh_var typ in
                            let field i =
                                let selectee = E.at pos typ (E.use var) in
                                let label = CCVector.get labels i in
                                let coerce = CCVector.get field_cos i |> Option.value ~default: Coercer.id in
                                let super = CCVector.get super_fields i in
                                let selection = E.at pos super (E.select selectee label) in
                                (label, Coercer.apply coerce selection) in
                            let base = E.at pos typ (E.use var) in
                            let body = E.at pos super (E.where base (Array.init fields_len field)) in
                            E.at pos super (E.let' [|Def (pos, var, expr)|] body)))
                    else None in

                let coercion = match co with
                    | Some co -> (match coerce with
                        | Some coerce -> (match super_co with
                            | Some super_co ->
                                let typ' = Stream.from (Source.zip
                                        (labels |> CCVector.to_seq |> Source.seq)
                                        (fields |> CCVector.to_seq |> Source.seq))
                                    |> Stream.into (Sink.fold (fun base (label, field) ->
                                        T.With {base; label; field}) base) in
                                Some (Coercer.coercer (fun expr ->
                                    let castee = Coercer.apply coerce (E.at pos typ' (E.cast expr co)) in
                                    E.at pos super (E.cast castee (Symm super_co))))
                            | None -> Some (Coercer.coercer (fun expr ->
                                Coercer.apply coerce (E.at pos super (E.cast expr co)))))
                        | None -> (match super_co with
                            | Some super_co -> Some (Coercer.coercer (fun expr ->
                                E.at pos super (E.cast expr (Trans (co, Symm super_co)))))
                            | None -> Some (Coercer.coercer (fun expr ->
                                E.at pos super (E.cast expr co)))))
                    | None -> (match coerce with
                        | Some coerce -> (match super_co with
                            | Some super_co -> Some (Coercer.coercer (fun expr ->
                                E.at pos super (E.cast (Coercer.apply coerce expr) (Symm super_co))))
                            | None -> Some coerce)
                        | None -> (match super_co with
                            | Some super_co -> Some (Coercer.coercer (fun expr ->
                                E.at pos super (E.cast expr super_co)))
                            | None -> None)) in
                {coercion; residual}
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (With _, _) -> (match super with
            | With _ ->
                let (labels, _, base, fields, super_base, super_fields, _) =
                    match_rows pos env typ super in

                let fields_len = CCVector.length labels in
                let {coercion = _; residual} = subtype pos occ env base super_base in
                let residual =
                    let rec loop residual i =
                        if i < fields_len
                        then begin
                            let {coercion = _; residual = residual'} =
                                subtype pos occ env (CCVector.get fields i) (CCVector.get super_fields i) in
                            loop (combine residual residual') (i + 1)
                        end else residual in
                    loop residual 0 in
                { coercion = None (* NOTE: Row types have no values so this will not get used *)
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (EmptyRow, _) -> (match super with
            | EmptyRow -> {coercion = None; residual = empty}
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (Proxy carrie, _) -> (match super with
            | Proxy carrie' ->
                let (let+) = Fun.flip Option.map in
                (* NOTE: Has the same structure as `K.eval`: *)
                let rec leftmost_callee max_uv_level = function
                    | T.App (callee, arg) ->
                        let (param, substitution, max_uv_level) = match arg with
                            | T.Ov ((name, kind), level) ->
                                (kind, Name.Map.singleton name 0, level)
                            | _ -> failwith "non-ov HKT arg" in
                        let+ (uv, callee) = leftmost_callee max_uv_level callee in
                        (uv, T.Fn (param, Env.close env substitution callee)) (* OPTIMIZE: `close`ing repeatedly *)
                    | Uv uv -> (match Env.get_uv env uv with
                        | Unassigned (_, _, level) ->
                            check_uv_assignee pos env uv level max_uv_level carrie;
                            Some (uv, carrie)
                        | Assigned typ -> leftmost_callee max_uv_level typ)
                    | _ -> todo (Some pos) in
                (match leftmost_callee Int.max_int carrie' with
                | Some (uv, impl) ->
                    Env.set_uv env pos uv (Assigned impl);
                    let expr = E.at pos super (E.proxy carrie') in
                    {coercion = Some (Coercer.coercer (fun _ -> expr)); residual = empty}
                | None -> (* TODO: Use unification (?) *)
                    let {coercion = coerce; residual} = subtype pos occ env carrie carrie' in
                    let {coercion = coerce'; residual = residual'} = subtype pos occ env carrie' carrie in
                    let expr = E.at pos super (E.proxy carrie') in
                    { coercion = (match (coerce, coerce') with
                        | (None, None) -> None
                        | _ -> Some (Coercer.coercer (fun _ -> expr)))
                    ; residual = combine residual residual' })

            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (App _, _) -> (match super with
            | App _ ->
                let {coercion; residual} = unify_whnf pos env typ super in
                { coercion = coercion |> Option.map (fun co ->
                    Coercer.coercer (fun v -> E.at pos super (E.cast v co)))
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (Ov _, _) -> (match super with
            | Ov _ ->
                let {coercion; residual} = unify_whnf pos env typ super in
                { coercion = coercion |> Option.map (fun co ->
                    Coercer.coercer (fun v -> E.at pos super (E.cast v co)))
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (Prim pt, _) -> (match super with
            | Prim pt' when Prim.eq pt pt' -> {coercion = None; residual = empty}
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = None; residual = empty})

        | (Fn _, _) -> unreachable (Some pos) ~msg: "Fn in subtype_whnf"
        | (Bv _, _) -> unreachable (Some pos) ~msg: "Bv in subtype_whnf" in

    let (>>=) = Option.bind in
    let res =
        K.eval pos env typ >>= fun (typ', co) ->
        K.eval pos env super |> Option.map (fun (super', co') ->
            let {coercion = coerce; residual} = subtype_whnf occ typ' super' in
            { coercion =
                (match (co, coerce, co') with
                | (Some co, Some coerce, Some co') -> Some (Coercer.coercer (fun v ->
                    let castee = Coercer.apply coerce (E.at pos typ' (E.cast v co)) in
                    E.at pos super (E.cast castee (Symm co'))))
                | (Some co, Some coerce, None) -> Some (Coercer.coercer (fun v ->
                    Coercer.apply coerce (E.at pos typ' (E.cast v co))))
                | (Some co, None, Some co') -> Some (Coercer.coercer (fun v ->
                    E.at pos super (E.cast v (Trans (co, Symm co')))))
                | (Some co, None, None) -> Some (Coercer.coercer (fun v ->
                    E.at pos super (E.cast v co)))
                | (None, Some coerce, Some co') -> Some (Coercer.coercer (fun v ->
                    E.at pos super (E.cast (Coercer.apply coerce v) (Symm co'))))
                | (None, Some coerce, None) -> Some coerce
                | (None, None, Some co') -> Some (Coercer.coercer (fun v ->
                    E.at pos super (E.cast v co')))
                | (None, None, None) -> None)
            ; residual }) in
    match res with
    | Some res -> res
    | None ->
        let patchable = ref (E.at pos super (E.const (Int 0))) in
        { coercion = Some (Coercer.coercer (fun v ->
            Env.set_expr env patchable v;
            E.at pos super (E.patchable patchable)))
        ; residual = Some (Sub (occ, typ, super, patchable)) }

and occurs_check pos env uv typ =
    let rec check : T.t -> unit = function
        | Exists (_, body) -> check body
        | PromotedArray typs -> Vector.iter check typs
        | PromotedTuple typs -> Vector.iter check typs
        | Tuple typs -> Vector.iter check typs
        | Pi {universals = _; domain; eff; codomain} -> check domain; check eff; check codomain
        | Impli {universals = _; domain; codomain} -> check domain; check codomain
        | Record row -> check row
        | With {base; label = _; field} -> check base; check field
        | EmptyRow -> ()
        | Proxy carrie -> check carrie
        | Fn (_, body) -> check body
        | App (callee, arg) -> check callee; check arg
        | Ov ov ->
            (match Env.get_implementation env ov with
            | Some (_, _, uv') -> check (Uv uv')
            | None -> ())
        | Uv uv' ->
            (match Env.get_uv env uv' with
            | Unassigned _ ->
                if uv = uv'
                then Env.reportError env pos (Occurs (uv, typ))
                else ()
            | Assigned typ -> check typ)
        | Bv _ | Prim _ -> () in
    check typ

(* # Unification *)

and unify pos env typ typ' : T.coercion option matching =
    let (>>=) = Option.bind in
    let res =
        K.eval pos env typ >>= fun (typ, co) ->
        K.eval pos env typ' |> Option.map (fun (typ', co'') ->
        let {coercion = co'; residual} = unify_whnf pos env typ typ' in
        { coercion =
            (match (co, co', co'') with
            | (Some co, Some co', Some co'') -> Some (T.Trans (Trans (co, co'), Symm co''))
            | (Some co, Some co', None) -> Some (Trans (co, co'))
            | (Some co, None, Some co'') -> Some (Trans (co, Symm co''))
            | (Some co, None, None) -> Some co
            | (None, Some co', Some co'') -> Some (Trans (co', Symm co''))
            | (None, Some co', None) -> Some co'
            | (None, None, Some co'') -> Some (Symm co'')
            | (None, None, None) -> None)
        ; residual }) in
    match res with
    | Some res -> res
    | None ->
        let patchable = ref (T.Refl typ') in
        { coercion = Some (T.Patchable patchable)
        ; residual = Some (Unify (typ, typ', patchable)) }

and unify_whnf : span -> Env.t -> T.t -> T.t -> T.coercion option matching
= fun pos env typ typ' ->
    let open ResidualMonoid in
    match (typ, typ') with
    (* TODO: uv impredicativity clashes: *)
    | (Uv uv, typ') | (typ', Uv uv) ->
        (match Env.get_uv env uv with
        | Unassigned (_, _, level) -> (* FIXME: use uv kind *)
            check_uv_assignee pos env uv level Int.max_int typ';
            Env.set_uv env pos uv (Assigned typ');
            {coercion = None; residual = empty}
        | Assigned _ -> unreachable (Some pos) ~msg: "Assigned `typ` in `unify_whnf`")

    | (Exists _, _) -> (match typ' with
        | Exists _ -> todo (Some pos)
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (PromotedArray typs, _) -> (match typ' with
        | PromotedArray typs' ->
            if Vector.length typs = Vector.length typs' then begin
                let coercions = CCVector.create () in
                let (residual, noop) = Vector.fold2 (fun (residual, noop) typ typ' ->
                    let {coercion; residual = residual'} = unify pos env typ typ' in
                    CCVector.push coercions coercion;
                    (combine residual residual', noop && Option.is_none coercion)
                ) (empty, true) typs typs' in
                { coercion = if noop
                    then Some (PromotedArrayCo (coercions |> CCVector.mapi (fun i -> function
                        | Some coercion -> coercion
                        | None -> T.Refl (Vector.get typs' i)
                    ) |> Vector.build))
                    else None
                ; residual }
            end else failwith "~ promoted array lengths"
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (PromotedTuple typs, _) -> (match typ' with
        | PromotedTuple typs' ->
            if Vector.length typs = Vector.length typs' then begin
                let coercions = CCVector.create () in
                let (residual, noop) = Vector.fold2 (fun (residual, noop) typ typ' ->
                    let {coercion; residual = residual'} = unify pos env typ typ' in
                    CCVector.push coercions coercion;
                    (combine residual residual', noop && Option.is_none coercion)
                ) (empty, true) typs typs' in
                { coercion = if noop
                    then Some (PromotedTupleCo (coercions |> CCVector.mapi (fun i -> function
                        | Some coercion -> coercion
                        | None -> T.Refl (Vector.get typs' i)
                    ) |> Vector.build))
                    else None
                ; residual }
            end else failwith "~ promoted values lengths"
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Tuple typs, _) -> (match typ' with
        | Tuple typs' ->
            if Vector.length typs = Vector.length typs' then begin
                let coercions = CCVector.create () in
                let (residual, noop) = Vector.fold2 (fun (residual, noop) typ typ' ->
                    let {coercion; residual = residual'} = unify pos env typ typ' in
                    CCVector.push coercions coercion;
                    (combine residual residual', noop && Option.is_none coercion)
                ) (empty, true) typs typs' in
                { coercion = if not noop
                    then Some (TupleCo (coercions |> CCVector.mapi (fun i -> function
                        | Some coercion -> coercion
                        | None -> T.Refl (Vector.get typs' i)
                    ) |> Vector.build))
                    else None
                ; residual }
            end else failwith "~ tuple lengths"
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Pi _, _) -> (match typ' with
        | Pi _ -> todo (Some pos)
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Impli _, _) -> (match typ' with
        | Impli _ -> todo (Some pos)
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Record row, _) -> (match typ' with
        | Record row' ->
            let {coercion = row_coercion; residual} = unify pos env row row' in
            {coercion = Option.map (fun co -> T.RecordCo co) row_coercion; residual}
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (With _, _) -> (match typ' with
        | With _ ->
            let (labels, co, base, fields, base', fields', co') = match_rows pos env typ typ' in

            let fields_len = CCVector.length labels in
            let {coercion = base_co; residual} = unify pos env base base' in
            let field_cos = CCVector.create_with ~capacity: fields_len base_co in
            let (residual, noop_fieldcos) =
                let rec loop residual noop_fieldcos i =
                    if i < fields_len
                    then begin
                        let {coercion = field_co; residual = residual'} =
                            unify pos env (CCVector.get fields i) (CCVector.get fields' i) in
                        CCVector.push field_cos field_co;
                        let noop_fieldcos = noop_fieldcos && Option.is_none field_co in
                        loop (combine residual residual') noop_fieldcos (i + 1)
                    end else (residual, noop_fieldcos) in
                loop residual true 0 in
            
            let rec build_coercion base i =
                if i < fields_len
                then build_coercion (T.WithCo {base
                    ; label = CCVector.get labels i
                    ; field = match CCVector.get field_cos i with
                        | Some field -> field
                        | None -> Refl (CCVector.get fields' i)})
                    (i + 1)
                else base in
            let co'' = match (base_co, noop_fieldcos) with
                | (Some base_co, _) -> Some (build_coercion base_co 0)
                | (None, false) -> Some (build_coercion (Refl base) 0)
                | (None, true) -> None in

            let coercion = match (co, co'', co') with
                | (Some co, Some co', Some co'') -> Some (T.Trans (Trans (co, co'), Symm co''))
                | (Some co, Some co', None) -> Some (Trans (co, co'))
                | (Some co, None, Some co'') -> Some (Trans (co, Symm co''))
                | (Some co, None, None) -> Some co
                | (None, Some co', Some co'') -> Some (Trans (co', Symm co''))
                | (None, Some co', None) -> Some co'
                | (None, None, Some co'') -> Some (Symm co'')
                | (None, None, None) -> None in
            {coercion; residual}
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (EmptyRow, _) -> (match typ' with
        | EmptyRow -> {coercion = None; residual = empty}
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Proxy carrie, _) -> (match typ' with
        | Proxy carrie' -> 
            let {coercion; residual} = unify pos env carrie carrie' in
            {coercion = Option.map (fun co -> T.ProxyCo co) coercion; residual}
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (T.App (callee, arg), _) -> (match typ' with
        | T.App (callee', arg') ->
            (* NOTE: Callees must already be in WHNF because of the Krivine-style `K.eval`: *)
            let {coercion = callee_co; residual} = unify_whnf pos env callee callee' in
            let {coercion = arg_co; residual = residual'} = unify pos env arg arg' in
            { coercion = (match (callee_co, arg_co) with
                | (Some callee_co, Some arg_co) -> Some (Comp (callee_co, Vector1.singleton arg_co))
                | (Some callee_co, None) -> Some (Comp (callee_co, Vector1.singleton (T.Refl arg')))
                | (None, Some arg_co) -> Some (Comp (Refl callee', Vector1.singleton arg_co))
                | (None, None) -> None)
            ; residual = combine residual residual' }
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Ov ov, _) -> (match typ' with
        | Ov ov' when ov = ov' -> {coercion = None; residual = empty}
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Prim pt, _) -> (match typ' with
        | Prim pt' when Prim.eq pt pt'-> {coercion = None; residual = empty}
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Fn _, _) -> unreachable (Some pos) ~msg: "Fn in unify_whnf"
    | (Bv _, _) -> unreachable (Some pos) ~msg: "Bv in unify_whnf"

(* Occurs check, ov escape check, HKT capturability check and uv level updates.
   Complected for speed. *)
and check_uv_assignee pos env uv level max_uv_level typ =
    let rec check : T.t -> unit = function
        | Exists (_, body) -> check body
        | PromotedArray typs -> Vector.iter check typs
        | PromotedTuple typs -> Vector.iter check typs
        | Tuple typs -> Vector.iter check typs
        | Pi {universals = _; domain; eff; codomain} -> check domain; check eff; check codomain
        | Impli {universals = _; domain; codomain} -> check domain; check codomain
        | Record row -> check row
        | With {base; label = _; field} -> check base; check field
        | EmptyRow -> ()
        | Proxy carrie -> check carrie
        | Fn (_, body) -> check body
        | App (callee, arg) -> check callee; check arg
        | Ov ((_, level') as ov) ->
            (match Env.get_implementation env ov with
            | Some (_, _, uv') -> check (Uv uv')
            | None ->
                if level' <= level
                then ()
                else Env.reportError env pos (Escape ov))
        | Uv uv' ->
            (match Env.get_uv env uv' with
            | Unassigned (name, kind, level') ->
                if uv = uv'
                then Env.reportError env pos (Occurs (uv, typ))
                else if level' <= level
                then ()
                else if level' <= max_uv_level
                then Env.set_uv env pos uv' (Unassigned (name, kind, level)) (* hoist *)
                else Env.reportError env pos (IncompleteImpl (uv, uv'))
            | Assigned typ -> check typ)
        | Bv _ | Prim _ -> () in
    check typ

(* # Constraint Solving *)

and solve pos env residual =
    let open Residual in
    let rec solve env = function
        | Axioms (axiom_bindings, residual) ->
            let env = Env.push_axioms env (Vector1.to_vector axiom_bindings) in
            solve env residual

        | Skolems (skolems, residual) ->
            let (env, _) = Env.push_skolems env (Vector1.to_vector skolems) in
            solve env residual

        | Residuals (residual, residual') ->
            ResidualMonoid.combine (solve env residual) (solve env residual')

        | Sub (occ, typ, super, patchable) ->
            let {coercion = coerce; residual} = subtype pos occ env typ super in
            let coerce = Option.value ~default: Coercer.id coerce in
            Env.set_expr env patchable (Coercer.apply coerce !patchable);
            residual

        | Unify (typ, typ', patchable) ->
            let {coercion; residual} = unify pos env typ typ' in
            Option.iter (Env.set_coercion env patchable) coercion;
            residual
    in
    (match Option.bind residual (solve env) with
    | None -> ()
    | Some residual -> Env.reportError env pos (Unsolvable residual))

(* Public API *)
(* NOTE: `focalize` is also public *)

let solving_subtype pos env typ super =
    let {coercion = coerce; residual} = subtype pos true env typ super in
    solve pos env residual;
    coerce

let solving_unify pos env typ super =
    let {coercion; residual} = unify pos env typ super in
    solve pos env residual;
    coercion

end

