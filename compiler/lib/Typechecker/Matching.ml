(*open Streaming*)
open Asserts

let ref = TxRef.ref
let (!) = TxRef.(!)
let (:=) = TxRef.(:=)

module Make
    (Env : TyperSigs.ENV)
    (K : TyperSigs.KINDING with type env = Env.t)
: TyperSigs.MATCHING with type env = Env.t
= struct

module T = ComplexFc.Type
module Uv = ComplexFc.Types.Uv
module Ov = ComplexFc.Types.Ov
module Binder = Uv.Binder
module E = ComplexFc.Term.Expr
(*module Err = TypeError*)

type env = Env.t
(*type span = Util.span

type 'a matching = {coercion : 'a; residual : Residual.t option}

let ref = TxRef.ref
let (!) = TxRef.(!)
let sibling = Env.sibling

let trans_with =
    let (let* ) = Option.bind in
    let (let+) = Fun.flip Option.map in
fun co base label field ->
    let* co = co in
    let+ base = base in
    T.Trans (co, WithCo {base; label; field = Refl field})

(* Massage `typ` into a `With`, returning `(coercion, base, field_t)`: *)
let pull_row pos env label' typ : T.t T.coercion option * T.t * T.t =
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
            (*let template = T.WithL {base = Hole; label = label'; field = Hole} in*)
            let () = todo (Some pos) (* Env.reportError env pos (Unusable (template, typ))*) in
            (None, Uv (Env.uv env T.aRow), Uv (Env.uv env T.aType))
        | None -> todo (Some pos) ~msg: "pull_row None" in
    pull typ

let match_rows : Util.span -> Env.t -> T.t -> T.t -> Name.t CCVector.ro_vector
    * T.t T.coercion option * T.t * T.t CCVector.ro_vector
    * T.t * T.t CCVector.ro_vector * T.t T.coercion option
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

(* # Resolution *)

let rec resolve pos env super =
    let results = Env.implicits env
        |> Stream.map (fun ({E.vtyp; name = _} as var) ->
            try Env.transaction env (fun () ->
                Some (var, subtype pos env vtyp super)
            ) with TypeError.TypeError _ -> None)
        |> Stream.flat_map (fun ores -> ores |> Option.to_seq |> Source.seq |> Stream.from)
        |> Stream.into (Vector.sink ()) in
    match Vector.length results with
    | 1 ->
        let (var, {coercion; residual}) = Vector.get results 0 in
        let expr = E.at pos var.vtyp (E.use var) in
        ( (match coercion with
          | Some coercion -> Coercer.apply coercion expr
          | None -> expr)
        , residual )
    | 0 -> todo (Some pos) ~msg: "resolution did not find"
    | _ -> todo (Some pos) ~msg: "ambiguous resolution"
*)

let rec unify : Util.span -> Env.t -> T.t -> T.t -> unit
=
    let articulate span env t (uv : Uv.t) t' =
        (*unify span env kind (K.kindof span env t);*)
        check_uv_assignee span env t !(uv.binder) Int.max_int t';
        Uv.graft_mono uv t' in

    let merge t (uv : Uv.t) binder t' (uv' : Uv.t) binder' =
        if Binder.level binder < Binder.level binder'
        then begin
            !(uv'.bindees) |> Vector.iter (fun bindee -> Uv.rebind bindee (Type uv));
            Uv.graft_mono uv' t
        end else begin
            !(uv.bindees) |> Vector.iter (fun bindee -> Uv.rebind bindee (Type uv'));
            Uv.graft_mono uv t'
        end in

    let subsume span env t (uv : Uv.t) t' = match !(uv.bound) with
        | Uv.Bot _ -> articulate span env t uv t'
        | Flex {typ; coerce = _} -> Env.in_bound env uv (fun env -> unify span env typ t');
        | Rigid _ -> (* Must be polymorphic while t' must be a monotype: *)
            Env.reportError env span (Unify (t, t')) in

    let unify_schemes span env t (uv : Uv.t) t' (uv' : Uv.t) =
        match (!(uv.bound), !(uv'.bound)) with
        | (Uv.Bot _, Uv.Bot _) ->
            (*unify span env kind kind';*)
            merge t uv !(uv.binder) t' uv' !(uv'.binder)

        | (Bot _, _) -> articulate span env t uv t'
        | (_, Bot _) -> articulate span env t' uv' t

        | (Flex {typ = t; coerce = _}, Flex {typ = t'; coerce = _}) ->
            Env.in_bounds env uv uv' (fun env -> unify span env t t');
            merge t uv !(uv.binder) t' uv' !(uv'.binder)

        | (Flex {typ = t; coerce = _}, Rigid {typ = t'; coerce = _}) ->
            Env.in_bounds env uv uv' (fun env -> unify span env t t');
            !(uv.bindees) |> Vector.iter (fun bindee -> Uv.rebind bindee (Type uv'));
            Uv.graft_mono uv t'
        | (Rigid {typ = t; coerce = _}, Flex {typ = t'; coerce = _}) ->
            Env.in_bounds env uv uv' (fun env -> unify span env t t');
            !(uv'.bindees) |> Vector.iter (fun bindee -> Uv.rebind bindee (Type uv));
            Uv.graft_mono uv' t

        | (Rigid {typ = t; coerce = _}, Rigid {typ = t'; coerce = _}) ->
            Env.in_bounds env uv uv' (fun env -> unify span env t t');
            merge t uv !(uv.binder) t' uv' !(uv'.binder) in

    let unify_whnf span env t t' = match (t, t') with
        | (T.Uv uv, t') | (t', T.Uv uv) ->
            if not (Uv.is_locked uv)
            then (match t' with (* OPTIMIZE: path compression, ranking (but mind bindees!) *)
                | T.Uv uv' when not (Uv.is_locked uv') ->
                    if Uv.equal uv uv'
                    then ()
                    else unify_schemes span env t uv t' uv'

                | t' -> subsume span env t uv t')
            else (match t' with
                | T.Uv uv' ->
                    if not (Uv.is_locked uv)
                    then todo (Some span) ~msg: "bv-uv'"
                    else if Uv.equal uv uv'
                        then ()
                        else Env.reportError env span (Unify (t, t'))

                | _ -> Env.reportError env span (Unify (t, t')))

        | (Ov ov, t') -> (match t' with
            | Ov ov' when Ov.equal ov ov' -> ()
            | _ -> Env.reportError env span (Unify (t, t')))

        | (Pi {domain; eff; codomain}, t') -> (match t' with
            | Pi {domain = domain'; eff = eff'; codomain = codomain'} ->
                unify span env domain domain';
                unify span env eff eff';
                unify span env codomain codomain'

            | _ -> Env.reportError env span (Unify (t, t')))

        | (Record row, t') -> (match t' with
            | Record row' -> unify span env row row'
            | _ -> Env.reportError env span (Unify (t, t')))

        | (EmptyRow, t') -> (match t' with
            | EmptyRow -> ()
            | _ -> Env.reportError env span (Unify (t, t')))

        | (Tuple typs, t') -> (match t' with
            | Tuple typs' -> Vector.iter2 (unify span env) typs typs'
            | _ -> Env.reportError env span (Unify (t, t')))

        | (PromotedTuple typs, t') -> (match t' with
            | PromotedTuple typs' -> Vector.iter2 (unify span env) typs typs'
            | _ -> Env.reportError env span (Unify (t, t')))

        | (PromotedArray typs, t') -> (match t' with
            | PromotedArray typs' -> Vector.iter2 (unify span env) typs typs'
            | _ -> Env.reportError env span (Unify (t, t')))

        (* TODO: Fancy HKT stuff: *)
        | (Proxy carrie, t') -> (match t' with
            | Proxy carrie' -> unify span env carrie carrie'
            | _ -> Env.reportError env span (Unify (t, t')))

        | (Prim pt, t') -> (match t' with
            | T.Prim pt' when Prim.eq pt pt'-> ()
            | _ -> Env.reportError env span (Unify (t, t')))

        | (t, t') -> todo (Some span)
            ~msg: ("type ctors "
                ^ (Util.doc_to_string (PPrint.(T.to_doc t ^/^ string "and" ^/^ T.to_doc t')))) in

    fun span env t t' ->
        unify_whnf span env (* OPTIMIZE: fst: *)
            (K.eval span env t |> Option.get |> fst) (* FIXME: Option.get *)
            (K.eval span env t' |> Option.get |> fst) (* FIXME: Option.get *)

and instance span env sub super = unify span env (Env.instantiate env sub) super

(*
(* # Focalization *)

and focalize : span -> Env.t -> T.t -> T.template -> Coercer.t option * T.t
= fun pos env typ template ->
    let articulate_template uv_typ template = match uv_typ with
        | T.Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                let (uv, typ) = match template with
                    | T.TupleL _ -> failwith "cannot articulate tuple; width unknown" in
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
                    (None, articulate_template typ template))) in

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

and subtype : span -> Env.t -> T.t -> T.t -> Coercer.t option matching
= fun pos env typ super ->
    let empty = ResidualMonoid.empty in
    let combine = ResidualMonoid.combine in

    let subtype_whnf : T.t -> T.t -> Coercer.t option matching
    = fun typ super -> match (typ, super) with
        (* TODO: uv impredicativity clashes *)
        (* FIXME: prevent nontermination from impredicative instantiation: *)
        | (Uv uv, Uv uv') when uv = uv' -> {coercion = None; residual = None}
        | (Uv uv, _) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                occurs_check pos env uv super;
                Env.set_uv env pos uv (Assigned super);
                {coercion = None; residual = empty}
            | Assigned _ -> unreachable (Some pos) ~msg: "Assigned `typ` in `subtype_whnf`")
        | (_, Uv uv) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                occurs_check pos env uv typ;
                Env.set_uv env pos uv (Assigned typ);
                {coercion = None; residual = empty}
            | Assigned _ -> unreachable (Some pos) ~msg: "Assigned `super` in `subtype_whnf`")

        | (Exists (existentials, body), _) ->
            let (env, skolems, typ) = Env.push_abs_skolems env existentials body in
            let {coercion = coerce; residual} = subtype pos env typ super in
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
            let {coercion = coerce; residual} = subtype pos env typ super in
            let existentials = Vector1.map (fun uv -> T.Uv uv) uvs |> Vector1.to_vector in
            { coercion = Some (Coercer.coercer (match coerce with
                | Some coerce -> (fun expr ->
                    E.at pos super (E.pack existentials (Coercer.apply coerce expr)))
                | None -> (fun expr -> E.at pos super (E.pack existentials expr))))
            ; residual }

        | (_, Impli {universals; domain; codomain}) ->
            let (env, skolems, domain, codomain) =
                Env.push_impli_skolems env universals domain codomain in
            let param = E.fresh_var domain in
            let env = Env.push_val Implicit env param in
            let {coercion = coerce_codomain; residual} =
                subtype pos env typ codomain in
            let universals = Vector.map fst skolems in
            { coercion = Some (Coercer.coercer (match coerce_codomain with
                | Some coerce_codomain -> (fun expr ->
                    let var = E.fresh_var codomain in
                    let value = Coercer.apply coerce_codomain expr in
                    let body = E.at pos codomain (E.use var) in
                    E.at pos super (E.let' [|Def (pos, var, value)|]
                        (E.at pos super (E.fn universals param body))))
                | None -> (fun expr -> E.at pos super (E.fn universals param expr))))
            ; residual }

        | (Impli {universals; domain; codomain}, _) ->
            let (uvs, domain, codomain) =
                Env.instantiate_impli env universals domain codomain in
            let {coercion = coerce_codomain; residual} =
                subtype pos env codomain super in
            let (arg, residual') = resolve pos env domain in
            let uvs = Vector.map (fun uv -> T.Uv uv) uvs in
            { coercion = Some (Coercer.coercer (match coerce_codomain with
                | Some coerce_codomain -> (fun expr ->
                    Coercer.apply coerce_codomain (E.at pos super (E.app expr uvs arg)))
                | None -> (fun expr -> E.at pos super (E.app expr uvs arg))))
            ; residual = combine residual residual' }

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
                            subtype pos env typ super in
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

        | (Pi {universals; domain; eff; codomain}, _) -> (match super with
            | Pi { universals = universals'; domain = domain'; eff = eff'; codomain = codomain'} ->
                let (env, universals', domain', eff', codomain') =
                    Env.push_arrow_skolems env universals' domain' eff' codomain' in
                let (uvs, domain, eff, codomain) =
                    Env.instantiate_arrow env universals domain eff codomain in
                let {coercion = coerce_domain; residual = residual} =
                    subtype pos env domain' domain in
                (* TODO: row opening à la Koka: *)
                let {coercion = _; residual = eff_residual} = unify pos env eff eff' in
                let residual = combine residual eff_residual in
                let {coercion = coerce_codomain; residual = codomain_residual} =
                    subtype pos env codomain codomain' in
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
                let {coercion = _; residual} = subtype pos env base super_base in
                let field_cos = CCVector.create_with ~capacity: fields_len None in
                let (residual, noop_fieldcos) =
                    let rec loop residual noop_fieldcos i =
                        if i < fields_len
                        then begin
                            let {coercion = field_co; residual = residual'} =
                                subtype pos env (CCVector.get fields i) (CCVector.get super_fields i) in
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
                let {coercion = _; residual} = subtype pos env base super_base in
                let residual =
                    let rec loop residual i =
                        if i < fields_len
                        then begin
                            let {coercion = _; residual = residual'} =
                                subtype pos env (CCVector.get fields i) (CCVector.get super_fields i) in
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
                    let {coercion = coerce; residual} = subtype pos env carrie carrie' in
                    let {coercion = coerce'; residual = residual'} = subtype pos env carrie' carrie in
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
            let {coercion = coerce; residual} = subtype_whnf typ' super' in
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
        ; residual = Some (Sub (typ, super, patchable)) }

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

and unify pos env typ typ' : T.t T.coercion option matching =
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

and unify_whnf : span -> Env.t -> T.t -> T.t -> T.t T.coercion option matching
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

    | (Exists (existentials, body), _) -> (match typ' with
        | Exists (existentials', body') ->
            let (env, skolems, body) = Env.push_abs_skolems env existentials body in
            let (uvs, body') = Env.instantiate_abs env existentials' body' in

            let {coercion = body_co; residual} = unify pos env body body' in

            (let seen = OvHashSet.create 0 in
            uvs |> Vector1.iter (fun uv -> match Env.get_uv env uv with
                | Assigned (Ov ov) when Vector1.exists ((=) ov) skolems ->
                    if not (OvHashSet.mem seen ov)
                    then OvHashSet.insert seen ov
                    else failwith ("insufficiently abstract rhs at " ^ Util.span_to_string pos)
                | Assigned _ -> failwith ("insufficiently abstract lhs at " ^ Util.span_to_string pos)
                | Unassigned _ -> ()
            ));

            let subst = Vector1.foldi (fun subst i ((name, _), _) ->
                Name.Map.add name i subst
            ) Name.Map.empty skolems in
            let body_co : T.t T.coercion = match body_co with
                | Some body_co -> Env.close_coercion env subst body_co
                | None -> Refl body' in
            {coercion = Some (ExistsCo (existentials', body_co)); residual}
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

    | (Pi {universals; domain; eff; codomain}, _) -> (match typ' with
        | Pi {universals = universals'; domain = domain'; eff = eff'; codomain = codomain'} ->
            let (env, skolems, domain', eff', codomain') =
                Env.push_arrow_skolems env universals' domain' eff' codomain' in
            let (uvs, domain, eff, codomain) =
                Env.instantiate_arrow env universals domain eff codomain in

            let {coercion = domain_co; residual = domain_resi} = unify pos env domain' domain in
            let {coercion = _; residual = eff_resi} = unify pos env eff eff' in
            let {coercion = codomain_co; residual = codomain_resi} =
                unify pos env codomain' codomain in

            (let seen = OvHashSet.create 0 in
            uvs |> Vector.iter (fun uv -> match Env.get_uv env uv with
                | Assigned (Ov ov) when Vector.exists ((=) ov) skolems ->
                    if not (OvHashSet.mem seen ov)
                    then OvHashSet.insert seen ov
                    else failwith ("insufficiently polymorphic lhs at " ^ Util.span_to_string pos)
                | Assigned _ -> failwith ("insufficiently polymorphic rhs at " ^ Util.span_to_string pos)
                | Unassigned _ -> ()
            ));

            let subst = Vector.foldi (fun subst i ((name, _), _) ->
                Name.Map.add name i subst
            ) Name.Map.empty skolems in
            { coercion = Some (PiCo {universals = universals'
                ; domain = (match domain_co with
                    | Some domain_co -> Env.close_coercion env subst domain_co
                    | None -> Refl domain')
                ; codomain = (match codomain_co with
                    | Some codomain_co -> Env.close_coercion env subst codomain_co
                    | None -> Refl domain')})
            ; residual = domain_resi |> combine eff_resi |> combine codomain_resi }
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Impli {universals; domain; codomain}, _) -> (match typ' with
        | Impli {universals = universals'; domain = domain'; codomain = codomain'} ->
            let (env, skolems, domain', codomain') =
                Env.push_impli_skolems env universals' domain' codomain' in
            let (uvs, domain, codomain) =
                Env.instantiate_impli env universals domain codomain in

            let {coercion = domain_co; residual = domain_resi} = unify pos env domain' domain in
            let {coercion = codomain_co; residual = codomain_resi} =
                unify pos env codomain' codomain in

            (let seen = OvHashSet.create 0 in
            uvs |> Vector.iter (fun uv -> match Env.get_uv env uv with
                | Assigned (Ov ov) when Vector.exists ((=) ov) skolems ->
                    if not (OvHashSet.mem seen ov)
                    then OvHashSet.insert seen ov
                    else failwith ("insufficiently polymorphic lhs at " ^ Util.span_to_string pos)
                | Assigned _ -> failwith ("insufficiently polymorphic rhs at " ^ Util.span_to_string pos)
                | Unassigned _ -> ()
            ));

            let subst = Vector.foldi (fun subst i ((name, _), _) ->
                Name.Map.add name i subst
            ) Name.Map.empty skolems in
            { coercion = Some (PiCo {universals = universals'
                ; domain = (match domain_co with
                    | Some domain_co -> Env.close_coercion env subst domain_co
                    | None -> Refl domain')
                ; codomain = (match codomain_co with
                    | Some codomain_co -> Env.close_coercion env subst codomain_co
                    | None -> Refl domain')})
            ; residual = combine domain_resi codomain_resi }
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
*)
(* Occurs check, ov escape check, HKT capturability check and uv level updates.
   Complected for speed. *)
and check_uv_assignee pos env uv uv_binder max_uv_level typ =
    let rec check : T.t -> unit = function
        | PromotedArray typs -> Vector.iter check typs
        | PromotedTuple typs -> Vector.iter check typs
        | Tuple typs -> Vector.iter check typs
        | Pi {domain; eff; codomain} -> check domain; check eff; check codomain
        | Impli {domain; codomain} -> check domain; check codomain
        | Record row -> check row
        | With {base; label = _; field} -> check base; check field
        | EmptyRow -> ()
        | Proxy carrie -> check carrie
        (*| Fn (_, body) -> check body
        | App (callee, arg) -> check callee; check arg*)
        | Ov {binder; _} as t ->
            (*(match Env.get_implementation env ov with
            | Some (_, _, uv') -> check (Uv uv')
            | None ->*)
                if Uv.Scope.level binder <= Binder.level uv_binder
                then ()
                else Env.reportError env pos (Escape t)

        | Uv uv' as t ->
            (match !(uv'.bound) with
            | Bot _ -> ()
            | Flex {typ; _} | Rigid {typ; _} -> check typ);

            if t == uv
            then Env.reportError env pos (Occurs (uv, typ))
            else begin
                let level' = Binder.level !(uv'.binder) in
                if level' < 0
                then ()
                else if level' <= Binder.level uv_binder
                then ()
                else if level' <= max_uv_level
                then Uv.rebind uv' uv_binder
                else Env.reportError env pos (IncompleteImpl (uv, t))
            end

        | Prim _ -> ()
        | _ -> todo (Some pos) ~msg: "check_uv_assignee" in
    (* OPTIMIZE: fst: *)
    check (K.eval pos env typ |> Option.get |> fst) (* FIXME: Option.get *)

(* Public API *)

let unify span env t t' =
    let causes = ref [] in
    (let env = Env.with_error_handler env (fun _ err -> causes := err :: !causes) in
    unify span env t t');
    match !causes with
    | [] -> ()
    | causes -> Env.reportError env span (Causes (Unify (t, t'), List.rev causes))

end

