open Streaming

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
type coercer = TyperSigs.coercer

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
    let rec pull typ = match K.eval env typ with
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
        | None -> failwith "TODO: pull_row None" in
    pull typ

let match_rows : Util.span -> Env.t -> T.t -> T.t -> Name.t CCVector.ro_vector
    * T.coercion option * T.t * T.t CCVector.ro_vector
    * T.t * T.t CCVector.ro_vector * T.coercion option
= fun pos env row row' ->
    let labels = CCVector.create () in
    let fields = CCVector.create () in
    let fields' = CCVector.create () in
    let rec matchem row row' = match K.eval env row' with
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
        | None -> failwith "TODO: match_rows None" in
    let (co, base, base', co') = matchem row row' in
    ( CCVector.freeze labels
    , co, base, CCVector.freeze fields
    , base', CCVector.freeze fields', Option.map (fun co' -> T.Symm co') co')

(* # Focalization *)

let focalize : span -> Env.t -> T.t -> T.template -> coercer * T.t
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
                    | Hole -> failwith "unreachable: Hole as template in `articulate_template`" in
                Env.set_uv env pos uv (Assigned typ);
                typ
            | Assigned _ -> failwith "unreachable: `articulate_template` on assigned uv")
        | _ -> failwith "unreachable: `articulate_template` on non-uv" in

    let focalize_whnf typ = match typ with
        | T.Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ -> (TyperSigs.Cf Fun.id, articulate_template typ template)
            | Assigned _ -> failwith "unreachable: Assigned uv in `focalize`.")
        | _ ->
            (match template with
            | TupleL min_length ->
                (match typ with
                | Tuple typs when Vector.length typs >= min_length -> (Cf Fun.id, typ)
                | _ ->
                    Env.reportError env pos (Unusable (template, typ));
                    let typ : T.t = Uv (Env.uv env T.aType) in
                    (Cf Fun.id, articulate_template typ template))
            | PiL _ -> (* TODO: arity check (or to `typeof`/`App`?) *)
                (match typ with
                | Pi _ -> (Cf Fun.id, typ)
                | _ ->
                    Env.reportError env pos (Unusable (template, typ));
                    let typ : T.t = Uv (Env.uv env T.aType) in
                    (Cf Fun.id, articulate_template typ template))
            | ProxyL _ ->
                (match typ with
                | Proxy _ -> (Cf Fun.id, typ)
                | _ ->
                    let typ : T.t = Uv (Env.uv env T.aType) in
                    (Cf Fun.id, articulate_template typ template))
            | WithL {base = _; label; field = _} ->
                let (co, base, field) = pull_row pos env label typ in
                let cof = match co with
                    | Some co -> (fun castee ->
                        E.at pos (With {base; label; field}) (E.cast castee co))
                    | None -> Fun.id in
                (Cf cof, With {base; label; field})
            | Hole -> failwith "unreachable: Hole as template in `focalize`.") in

    match K.eval env typ with
    | Some (typ', coercion) ->
        let (Cf cf as coercer, typ) = focalize_whnf typ' in
        ( (match coercion with
          | Some coercion -> Cf (fun castee ->
                cf (E.at pos typ' (E.cast castee coercion)))
          | None -> coercer)
        , typ )
    | None -> failwith "unreachable: `whnf` failed in `focalize`."

(* # Subtyping *)

let rec subtype : span -> bool -> Env.t -> T.t -> T.t -> coercer matching
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
                        | Assigned _ -> failwith "unreachable: Assigned as template of `articulate`")

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

                    | Exists _ -> failwith "unreachable: `Exists` as template of `articulate`"
                    | Fn _ -> failwith "unreachable: `Fn` as template of `articulate`"
                    | Bv _ -> failwith "unreachable: `Bv` as template of `articulate`" in
                Env.set_uv env pos uv (Assigned typ);
                typ
            | Assigned _ -> failwith "unreachable: `articulate` on assigned uv")
        | _ -> failwith "unreachable: `articulate` on non-uv" in

    let subtype_whnf : bool -> T.t -> T.t -> coercer matching
    = fun occ typ super -> match (typ, super) with
        | (Impli _, _) | (_, Impli _) -> failwith "TODO"

        | (Exists (existentials, body), _) ->
            let (env, skolems, typ) = Env.push_abs_skolems env existentials body in
            let {coercion = Cf coerce; residual} = subtype pos occ env typ super in
            let skolems = Vector1.map fst skolems in
            { coercion = Cf (fun expr ->
                let var = E.fresh_var typ in
                let use = E.at pos var.vtyp (E.use var) in
                E.at pos super (E.unpack skolems var expr (coerce use)))
            ; residual = ResidualMonoid.skolemized (Vector.map snd (Vector1.to_vector skolems))
                residual }
        | (_, Exists (existentials', body')) ->
            let (uvs, super) = Env.instantiate_abs env existentials' body' in
            let {coercion = Cf coerce; residual} = subtype pos occ env typ super in
            let existentials = Vector1.map (fun uv -> T.Uv uv) uvs |> Vector1.to_vector in
            (* FIXME: coercing potentially nonatomic `expr`: *)
            { coercion = Cf (fun expr -> E.at pos super (E.pack existentials (coerce expr)))
            ; residual }

        (* TODO: uv <: Exists impredicativity clash *)

        | (Uv uv, Uv uv') when uv = uv' -> {coercion = Cf Fun.id; residual = None}
        | (Uv uv, _) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                if occ then occurs_check pos env uv super else ();
                subtype pos false env (articulate pos env typ super) super
            | Assigned _ -> failwith "unreachable: Assigned `typ` in `subtype_whnf`")
        | (_, Uv uv) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                if occ then occurs_check pos env uv typ else ();
                subtype pos false env typ (articulate pos env super typ)
            | Assigned _ -> failwith "unreachable: Assigned `super` in `subtype_whnf`")

        | (PromotedArray _, _) -> (match super with
            | PromotedArray _ ->
                let {coercion = _; residual} = unify pos env typ super in
                { coercion = Cf (fun _ -> failwith "Compiler bug: PromotedArray coercion called")
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

        | (PromotedTuple _, _) -> (match super with
            | PromotedTuple _ ->
                let {coercion = _; residual} = unify pos env typ super in
                { coercion = Cf (fun _ -> failwith "Compiler bug: PromotedTuple coercion called")
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

        | (Tuple typs, _) -> (match super with
            | Tuple super_typs ->
                if Vector.length typs = Vector.length super_typs then begin
                    let coercions = CCVector.create () in
                    (* OPTIMIZE: `noop` as in unification: *)
                    let residual = Vector.fold2 (fun residual typ super ->
                        let {coercion = Cf coercion; residual = residual'} =
                            subtype pos occ env typ super in
                        CCVector.push coercions (typ, coercion);
                        combine residual residual'
                    ) empty typs super_typs in
                    { coercion = Cf (fun expr ->
                        let var = E.fresh_var typ in
                        let body = E.at pos super (E.values (coercions |> CCVector.mapi (fun i (typ, coerce) ->
                            let use = E.at pos typ (E.use var) in
                            coerce (E.at pos typ (E.focus use i))
                        ) |> CCVector.to_array)) in
                        E.at pos super (E.let' [|Def (pos, var, expr)|] body))
                    ; residual }
                end else failwith "<: tuple lengths"
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

        | (Pi {universals; domain; eff; codomain}, _) -> (match super with
            | Pi { universals = universals'; domain = domain'; eff = eff'; codomain = codomain'} ->
                let (env, universals', domain', eff', codomain') =
                    Env.push_arrow_skolems env universals' domain' eff' codomain' in
                let (uvs, domain, eff, codomain) =
                    Env.instantiate_arrow env universals domain eff codomain in
                let {coercion = Cf coerce_domain; residual = residual} =
                    subtype pos occ env domain' domain in
                (* TODO: row opening à la Koka: *)
                let {coercion = _; residual = eff_residual} = unify pos env eff eff' in
                let residual = combine residual eff_residual in
                let {coercion = Cf coerce_codomain; residual = codomain_residual} =
                    subtype pos occ env codomain codomain' in
                let residual = combine residual codomain_residual in

                let universals = Vector.map (fun uv -> T.Uv uv) uvs in
                let universals' = Vector.map fst universals' in
                let param = E.fresh_var domain' in
                let arg = coerce_domain (E.at pos domain' (E.use param)) in
                { coercion = TyperSigs.Cf (fun expr ->
                    let body = E.at pos codomain (E.app expr universals arg) in
                    let body = coerce_codomain body in
                    E.at pos super (E.fn universals' param body))
                ; residual = ResidualMonoid.skolemized (Vector.map snd universals') residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

        | (Record row, _) -> (match super with
            | Record super_row ->
                let (labels, co, base, fields, super_base, super_fields, super_co) =
                    match_rows pos env row super_row in

                let fields_len = CCVector.length labels in
                let {coercion = _; residual} = subtype pos occ env base super_base in
                let field_cos = CCVector.create_with ~capacity: fields_len (TyperSigs.Cf Fun.id) in
                let residual = (* OPTIMIZE: `noop_fieldcos` as in unification *)
                    let rec loop residual i =
                        if i < fields_len
                        then begin
                            let {coercion = field_co; residual = residual'} =
                                subtype pos occ env (CCVector.get fields i) (CCVector.get super_fields i) in
                            CCVector.push field_cos field_co;
                            loop (combine residual residual') (i + 1)
                        end else residual in
                    loop residual 0 in

                let coerce = match super_base with
                | EmptyRow -> (fun expr ->
                    let var = E.fresh_var typ in
                    let field i =
                        let selectee = E.at pos typ (E.use var) in
                        let label = CCVector.get labels i in
                        let Cf coerce = CCVector.get field_cos i in
                        let super = CCVector.get super_fields i in
                        let selection = E.at pos super (E.select selectee label) in
                        (label, coerce selection) in
                    let body = E.at pos super (E.record (Array.init fields_len field)) in
                    E.at pos super (E.let' [|Def (pos, var, expr)|] body))
                | _ -> (fun expr ->
                    let var = E.fresh_var typ in
                    let field i =
                        let selectee = E.at pos typ (E.use var) in
                        let label = CCVector.get labels i in
                        let Cf coerce = CCVector.get field_cos i in
                        let super = CCVector.get super_fields i in
                        let selection = E.at pos super (E.select selectee label) in
                        (label, coerce selection) in
                    let base = E.at pos typ (E.use var) in
                    let body = E.at pos super (E.where base (Array.init fields_len field)) in
                    E.at pos super (E.let' [|Def (pos, var, expr)|] body)) in

                { coercion = (match (co, super_co) with
                    | (Some co, Some super_co) ->
                        let typ' = Stream.from (Source.zip
                                (labels |> CCVector.to_seq |> Source.seq)
                                (fields |> CCVector.to_seq |> Source.seq))
                            |> Stream.into (Sink.fold (fun base (label, field) ->
                                T.With {base; label; field}) base) in
                        TyperSigs.Cf (fun v ->
                            let castee = coerce (E.at pos typ' (E.cast v co)) in
                            E.at pos super (E.cast castee (Symm super_co)))
                    | (Some co, None) -> Cf (fun v ->
                        coerce (E.at pos super (E.cast v co)))
                    | (None, Some co') -> Cf (fun v ->
                        E.at pos super (E.cast (coerce v) (Symm co')))
                    | (None, None) -> Cf coerce)
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

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
                { coercion = Cf Fun.id (* NOTE: Row types have no values so this will not get used *)
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

        | (EmptyRow, _) -> (match super with
            | EmptyRow -> {coercion = Cf Fun.id; residual = empty}
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

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
                    | _ -> failwith "FIXME: leftmost_callee" in
                (match leftmost_callee Int.max_int carrie' with
                | Some (uv, impl) ->
                    Env.set_uv env pos uv (Assigned impl);
                    let expr = E.at pos super (E.proxy carrie') in
                    {coercion = Cf (fun _ -> expr); residual = empty}
                | None -> (* TODO: Use unification (?) *)
                    let {coercion = _; residual} = subtype pos occ env carrie carrie' in
                    let {coercion = _; residual = residual'} = subtype pos occ env carrie' carrie in
                    let expr = E.at pos super (E.proxy carrie') in
                    {coercion = Cf (fun _ -> expr); residual = combine residual residual'})

            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

        | (App _, _) -> (match super with
            | App _ ->
                let {coercion; residual} = unify_whnf pos env typ super in
                { coercion =
                    (match coercion with
                    | Some co -> Cf (fun v -> E.at pos super (E.cast v co))
                    | None -> Cf Fun.id)
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

        | (Ov _, _) -> (match super with
            | Ov _ ->
                let {coercion; residual} = unify_whnf pos env typ super in
                { coercion =
                    (match coercion with
                    | Some co -> Cf (fun v -> E.at pos super (E.cast v co))
                    | None -> Cf Fun.id)
                ; residual }
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

        | (Prim pt, _) -> (match super with
            | Prim pt' when Prim.eq pt pt' -> {coercion = Cf Fun.id; residual = empty}
            | _ ->
                Env.reportError env pos (SubType (typ, super));
                {coercion = Cf Fun.id; residual = empty})

        | (Fn _, _) -> failwith "unreachable: Fn in subtype_whnf"
        | (Bv _, _) -> failwith "unreachable: Bv in subtype_whnf" in

    let (>>=) = Option.bind in
    let res =
        K.eval env typ >>= fun (typ', co) ->
        K.eval env super |> Option.map (fun (super', co') ->
            let {coercion = Cf coerce; residual} = subtype_whnf occ typ' super' in
            { coercion =
                (match (co, co') with
                | (Some co, Some co') ->
                    TyperSigs.Cf (fun v ->
                        let castee = coerce (E.at pos typ' (E.cast v co)) in
                        E.at pos super (E.cast castee (Symm co')))
                | (Some co, None) -> Cf (fun v ->
                    coerce (E.at pos typ' (E.cast v co)))
                | (None, Some co') -> Cf (fun v ->
                    E.at pos super (E.cast (coerce v) (Symm co')))
                | (None, None) -> Cf coerce)
            ; residual }) in
    match res with
    | Some res -> res
    | None ->
        let patchable = ref (E.at pos super (E.const (Int 0))) in
        { coercion = Cf (fun v ->
            Env.set_expr env patchable v;
            E.at pos super (E.patchable patchable))
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
        K.eval env typ >>= fun (typ, co) ->
        K.eval env typ' |> Option.map (fun (typ', co'') ->
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
    | (Impli _, _) | (_, Impli _) -> failwith "TODO"

    | (Exists _, _) -> (match typ' with
        | Exists _ -> failwith "TODO: unify existentials"
        | _ ->
            Env.reportError env pos (Unify (typ, typ'));
            {coercion = None; residual = empty})

    | (Uv uv, typ') | (typ', Uv uv) ->
        (match Env.get_uv env uv with
        | Unassigned (_, _, level) -> (* FIXME: use uv kind *)
            check_uv_assignee pos env uv level Int.max_int typ';
            Env.set_uv env pos uv (Assigned typ');
            {coercion = None; residual = empty}
        | Assigned _ -> failwith "unreachable: Assigned `typ` in `unify_whnf`")

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
                { coercion = if noop
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
        | Pi _ -> failwith "TODO: unify Pi"
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

    | (Fn _, _) -> failwith "unreachable: Fn in unify_whnf"
    | (Bv _, _) -> failwith "unreachable: Bv in unify_whnf"

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
            let {coercion = Cf coerce; residual} = subtype pos occ env typ super in
            Env.set_expr env patchable (coerce !patchable);
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

let solving_subtype pos env typ super =
    let {coercion; residual} = subtype pos true env typ super in
    solve pos env residual;
    coercion

let solving_unify pos env typ super =
    let {coercion; residual} = unify pos env typ super in
    solve pos env residual;
    coercion

end

