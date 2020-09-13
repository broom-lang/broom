module ResidualMonoid = struct
    include Monoid.OfSemigroup(Residual)

    let skolemized skolems m = Option.map (fun r -> Residual.Skolems (skolems, r)) m
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
            let base = T.Uv (sibling env (Prim Row) uv) in
            let field = T.Uv (sibling env (Prim Type) uv) in
            Env.set_uv env uv (Assigned (With {base; label = label'; field}));
            (co, base, field)
        | Some _ ->
            let template = T.WithL {base = Hole; label = label'; field = Hole} in
            raise (Err.TypeError (pos, Unusable (template, typ)))
        | None -> failwith "TODO: pull_row None" in
    pull typ

let rec match_rows : Util.span -> Env.t -> T.t -> T.t -> Name.t CCVector.ro_vector
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

let rec focalize : span -> Env.t -> T.t -> T.template -> coercer * T.t
= fun pos env typ template ->
    let articulate_template uv_typ template = match uv_typ with
        | T.Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                let (uv, typ) = match template with
                    | T.PiL (arity, _) ->
                        (uv, T.Pi ( Vector.of_list []
                                  , Vector.init arity (fun _ -> T.Uv (sibling env (Prim Type) uv))
                                  , Uv (sibling env (Prim Type) uv), T.to_abs (Uv (sibling env (Prim Type) uv)) ))
                    | ProxyL _ -> (uv, T.Proxy (T.to_abs (Uv (sibling env (Prim Type) uv))))
                    | WithL {base = _; label; field = _} ->
                        (uv, (With {base = Uv (sibling env (Prim Row) uv)
                            ; label; field = Uv (sibling env (Prim Type) uv)}))
                    | Hole -> failwith "unreachable: Hole as template in `articulate_template`" in
                Env.set_uv env uv (Assigned typ);
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
            | PiL _ -> (* TODO: arity check (or to `typeof`/`App`?) *)
                (match typ with
                | Pi _ -> (Cf Fun.id, typ)
                | _ -> raise (Err.TypeError (pos, Unusable (template, typ))))
            | ProxyL _ ->
                (match typ with
                | Proxy _ -> (Cf Fun.id, typ)
                | _ -> raise (Err.TypeError (pos, Unusable (template, typ))))
            | WithL {base = _; label; field = _} ->
                let (co, base, field) = pull_row pos env label typ in
                let cof = match co with
                    | Some co -> (fun v -> {Util.v = E.Cast (v, co); pos})
                    | None -> Fun.id in
                (Cf cof, With {base; label; field})
            | Hole -> failwith "unreachable: Hole as template in `focalize`.") in

    match K.eval env typ with
    | Some (typ, coercion) ->
        let (Cf cf as coercer, typ) = focalize_whnf typ in
        ( (match coercion with
          | Some coercion -> TyperSigs.Cf (fun v -> cf {pos; v = Cast (v, coercion)})
          | None -> coercer)
        , typ )
    | None -> failwith "unreachable: `whnf` failed in `focalize`."

(* # Subtyping *)

let rec subtype_abs : span -> bool -> Env.t -> T.abs -> T.abs -> coercer matching
= fun pos occ env typ super ->
    let (env, skolems, typ) = Env.push_abs_skolems env typ in
    let (uvs, super) = Env.instantiate_abs env super in
    match Vector1.of_vector skolems with
    | Some skolems ->
        let skolems = Vector1.map fst skolems in
        (match Vector1.of_vector uvs with
        | Some uvs ->
            let {coercion = Cf coerce; residual} = subtype pos occ env typ super in

            let name = Name.fresh () in
            let impl = {E.name; typ} in
            let uvs = Vector1.map (fun uv -> T.Uv uv) uvs in
            let body = {Util.pos; v = E.Pack (uvs, coerce {Util.pos; v = Use name})} in
            { coercion = Cf (fun v -> {pos; v = Unpack (skolems, impl, v, body)})
            ; residual = ResidualMonoid.skolemized (Vector1.map snd skolems) residual }
        | None ->
            let {coercion = Cf coerce; residual} = subtype pos occ env typ super in

            let name = Name.fresh () in 
            let impl = {E.name; typ} in
            let body = coerce {Util.pos; v = Use name} in
            { coercion = Cf (fun v -> {pos; v = Unpack (skolems, impl, v, body)})
            ; residual = ResidualMonoid.skolemized (Vector1.map snd skolems) residual })

    | None ->
        (match Vector1.of_vector uvs with
        | Some uvs ->
            let {coercion = Cf coerce; residual} = subtype pos occ env typ super in

            let uvs = Vector1.map (fun uv -> T.Uv uv) uvs in
            {coercion = Cf (fun v -> {pos; v = Pack (uvs, coerce v)}); residual}
        | None -> subtype pos occ env typ super)

and subtype : span -> bool -> Env.t -> T.t -> T.t -> coercer matching
= fun pos occ env typ super ->
    let empty = ResidualMonoid.empty in
    let combine = ResidualMonoid.combine in

    let articulate pos occ env uv_typ template = match uv_typ with
        | T.Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned (_, kind, level) ->
                let (uv, typ) = match template with
                    | T.Uv uv' ->
                        (match Env.get_uv env uv' with
                        | Unassigned (_, kind', level') ->
                            if level' <= level
                            then (uv, template)
                            else (uv', uv_typ)
                        | Assigned _ -> failwith "unreachable: Assigned as template of `articulate`")

                    | Ov ((_, level') as ov) ->
                        if level' <= level
                        then (uv, Ov ov)
                        else raise (Err.TypeError (pos, Escape ov))

                    | Values typs ->
                        (uv, Values (Vector.map (fun typ ->
                            T.Uv (sibling env (K.kindof_F env typ) uv)
                        ) typs))
                    | Pi (_, domain, _, _) ->
                        (uv, Pi ( Vector.of_list []
                                , Vector.map (fun _ -> T.Uv (sibling env (Prim Type) uv)) domain
                                , Uv (sibling env (Prim Row) uv)
                                , T.to_abs (Uv (sibling env (Prim Type) uv)) ))
                    | Record _ -> (uv, Record (Uv (sibling env (Prim Row) uv)))
                    | With {base = _; label; field = _} ->
                        (uv, With {base = Uv (sibling env (Prim Row) uv); label; field = Uv (sibling env (Prim Type) uv)})
                    | EmptyRow -> (uv, EmptyRow)
                    | Proxy _ -> (uv, Proxy (T.to_abs (Uv (sibling env (failwith "TODO") uv))))
                    | App (callee, args) ->
                        ( uv, T.App (Uv (sibling env (K.kindof_F env callee) uv)
                        , Vector1.map (fun arg -> T.Uv (sibling env (K.kindof_F env arg) uv)) args) )
                    | Prim pt -> (uv, Prim pt)

                    | Fn _ -> failwith "unreachable: `Fn` as template of `articulate`"
                    | Bv _ -> failwith "unreachable: `Bv` as template of `articulate`" in
                Env.set_uv env uv (Assigned typ);
                typ
            | Assigned _ -> failwith "unreachable: `articulate` on assigned uv")
        | _ -> failwith "unreachable: `articulate` on non-uv" in

    let subtype_whnf : bool -> T.t -> T.t -> coercer matching
    = fun occ typ super -> match (typ, super) with
        | (Uv uv, Uv uv') when uv = uv' -> {coercion = Cf Fun.id; residual = None}
        | (Uv uv, _) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                if occ then occurs_check pos env uv super else ();
                subtype pos false env (articulate pos occ env typ super) super
            | Assigned _ -> failwith "unreachable: Assigned `typ` in `subtype_whnf`")
        | (_, Uv uv) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                if occ then occurs_check pos env uv typ else ();
                subtype pos false env typ (articulate pos occ env super typ)
            | Assigned _ -> failwith "unreachable: Assigned `super` in `subtype_whnf`")

        | (Values typs, _) -> (match super with
            | Values super_typs ->
                if Vector.length typs = Vector.length super_typs then begin
                    let coercions = CCVector.create () in
                    (* OPTIMIZE: `noop` as in unification: *)
                    let residual = Vector.fold2 (fun residual typ super ->
                        let {coercion = Cf coercion; residual = residual'} =
                            subtype pos occ env typ super in
                        CCVector.push coercions coercion;
                        combine residual residual'
                    ) empty typs super_typs in
                    { coercion = Cf (fun expr ->
                        let name = Name.fresh () in
                        let use = {Util.pos; v = E.Use name} in
                        let body = {Util.pos; v = E.Values (coercions |> CCVector.mapi (fun i coerce ->
                            coerce {Util.pos; v = E.Focus (use, i)}
                        ) |> Vector.build)} in
                        {pos; v = Let ((pos, {pos; v = UseP name}, expr), body)})
                    ; residual }
                end else failwith "<: tuple lengths"
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

        | (Pi (universals, domain, eff, codomain), _) -> (match super with
            | Pi (universals', domain', eff', codomain') ->
                let (env, universals', domain', eff', codomain') =
                    Env.push_arrow_skolems env universals' domain' eff' codomain' in
                let (uvs, domain, eff, codomain) =
                    Env.instantiate_arrow env universals domain eff codomain in

                (* FIXME: raises on arity mismatch: *)
                let {coercion = domain_coercions; residual = domain_residual} =
                    Vector.fold2 (fun {coercion = coercions; residual} domain domain' ->
                        let {coercion; residual = residual'} = subtype pos occ env domain' domain in
                        {coercion = coercion :: coercions; residual = combine residual residual'})
                    {coercion = []; residual = empty} domain domain' in
                let domain_coercions = domain_coercions |> List.rev |> Vector.of_list in
                let {coercion = _; residual = eff_residual} = subtype pos occ env eff eff' in
                let {coercion = Cf coerce_codomain; residual = codomain_residual} =
                    subtype_abs pos occ env codomain codomain' in

                let names = Vector.map (fun _ -> Name.fresh ()) domain in
                let params = Vector.map2 (fun name domain' -> {E.name; typ = domain'}) names domain' in
                let args = Vector.map2 (fun name (TyperSigs.Cf coerce_domain) ->
                        coerce_domain {pos; v = E.Use name}
                ) names domain_coercions in
                let arrows_residual = codomain_residual
                    |> combine eff_residual
                    |> combine domain_residual in
                { coercion = TyperSigs.Cf (fun v ->
                    let body = coerce_codomain {pos; v = App (v, Vector.map (fun uv -> T.Uv uv) uvs, args)} in
                    {pos; v = E.Fn (Vector.map fst universals', params, body)})
                ; residual =
                    (match Vector1.of_vector (Vector.map fst universals') with
                    | Some skolems -> ResidualMonoid.skolemized (Vector1.map snd skolems) arrows_residual
                    | None -> arrows_residual) }
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

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
                    let name = Name.fresh () in
                    let def = {Util.v = E.UseP name; pos} in
                    let use = {Util.v = E.Use name; pos} in
                    let field i =
                        let label = CCVector.get labels i in
                        let Cf coerce = CCVector.get field_cos i in
                        let selection = {Util.v = E.Select (use, label); pos} in
                        (label, coerce selection) in
                    let body = {Util.v = E.Record (Vector.init fields_len field); pos} in
                    {Util.v = E.Let ((pos, def, expr), body); pos})
                | _ -> (fun expr ->
                    let name = Name.fresh () in
                    let def = {Util.v = E.UseP name; pos} in
                    let use = {Util.v = E.Use name; pos} in
                    let field i =
                        let label = CCVector.get labels i in
                        let Cf coerce = CCVector.get field_cos i in
                        let selection = {Util.v = E.Select (use, label); pos} in
                        (label, coerce selection) in
                    (match Vector1.of_vector (Vector.init fields_len field) with
                    | Some fields ->
                        let body = {Util.v = E.Where (use, fields); pos} in
                        {Util.v = E.Let ((pos, def, expr), body); pos}
                    | None -> expr)) in

                { coercion = (match (co, super_co) with
                    | (Some co, Some super_co) ->
                        TyperSigs.Cf (fun v -> {pos; v = Cast (coerce {pos; v = Cast (v, co)}, Symm super_co)})
                    | (Some co, None) -> Cf (fun v -> coerce {pos; v = Cast (v, co)})
                    | (None, Some co') -> Cf (fun v -> {pos; v = Cast (coerce v, Symm co')})
                    | (None, None) -> Cf coerce)
                ; residual }
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

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
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

        | (EmptyRow, _) -> (match super with
            | EmptyRow -> {coercion = Cf Fun.id; residual = empty}
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

        (* TODO: DRY: *)
        | (Proxy (Exists (existentials, carrie) as abs_carrie), _) -> (match super with
            | Proxy (Exists (existentials', App (callee, args)) as abs_carrie') when Vector.length existentials' = 0 ->
                (match K.eval env callee with
                | Some (Uv uv, _) ->
                    (match Env.get_uv env uv with
                    | Unassigned (_, kind, level) ->
                        let substitution = Vector1.foldi (fun substitution i -> function
                            | T.Ov ((name, _), _) -> Name.Map.add name i substitution
                            | _ -> failwith "unreachable: non-ov path arg in path locator"
                        ) Name.Map.empty args in
                        let params = Vector1.map (function
                            | T.Ov ((_, kind), _) -> kind
                            | _ -> failwith "unreachable: non-ov path arg in path locator"
                        ) args in
                        let impl = T.Fn (params, Env.close env substitution carrie) in
                        let max_uv_level = match Vector1.get args 0 with
                            | Ov (_, level') -> level' - 1
                            | _ -> failwith "unreachable: non-ov path arg in path locator" in
                        check_uv_assignee pos env uv level max_uv_level impl;
                        Env.set_uv env uv (Assigned impl);
                        { coercion = TyperSigs.Cf (fun _ -> {v = Proxy abs_carrie'; pos})
                        ; residual = empty }
                    | _ -> failwith "unreachable: Assigned uv in Proxy <:")

                | _ -> (* TODO: Use unification (?) *)
                    let {coercion = _; residual} =
                        subtype_abs pos occ env abs_carrie abs_carrie' in
                    let {coercion = _; residual = residual'} =
                        subtype_abs pos occ env abs_carrie' abs_carrie in
                    { coercion = Cf (fun _ -> {v = Proxy abs_carrie'; pos})
                    ; residual = combine residual residual' })

            | Proxy abs_carrie' -> (* TODO: Use unification (?) *)
                let {coercion = _; residual} =
                    subtype_abs pos occ env abs_carrie abs_carrie' in
                let {coercion = _; residual = residual'} =
                    subtype_abs pos occ env abs_carrie' abs_carrie in
                { coercion = Cf (fun _ -> {v = Proxy abs_carrie'; pos})
                ; residual = combine residual residual' }

            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

        | (App _, _) -> (match super with
            | App _ ->
                let {coercion; residual} = unify_whnf pos env typ super in
                { coercion =
                    (match coercion with
                    | Some co -> Cf (fun v -> {pos; v = Cast (v, co)})
                    | None -> Cf Fun.id)
                ; residual }
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

        | (Ov _, _) -> (match super with
            | Ov _ ->
                let {coercion; residual} = unify_whnf pos env typ super in
                { coercion =
                    (match coercion with
                    | Some co -> Cf (fun v -> {pos; v = Cast (v, co)})
                    | None -> Cf Fun.id)
                ; residual }
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

        | (Prim pt, _) -> (match super with
            | Prim pt' when Prim.eq pt pt' -> {coercion = Cf Fun.id; residual = empty}
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

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
                    TyperSigs.Cf (fun v -> {pos; v = Cast (coerce {pos; v = Cast (v, co)}, Symm co')})
                | (Some co, None) -> Cf (fun v -> coerce {pos; v = Cast (v, co)})
                | (None, Some co') -> Cf (fun v -> {pos; v = Cast (coerce v, Symm co')})
                | (None, None) -> Cf coerce)
            ; residual }) in
    match res with
    | Some res -> res
    | None ->
        let patchable = ref {Util.pos; v = E.Const (Int 0)} in
        { coercion = Cf (fun v ->
            Env.set_expr env patchable v;
            {pos; v = Patchable patchable})
        ; residual = Some (Sub (occ, typ, super, patchable)) }

and occurs_check pos env uv typ =
    let rec check_abs (Exists (_, body) : T.abs) = check body

    and check = function
        | Values typs -> Vector.iter check typs
        | Pi (_, domain, eff, codomain) ->
            Vector.iter check domain;
            check eff;
            check_abs codomain
        | Record row -> check row
        | With {base; label = _; field} -> check base; check field
        | EmptyRow -> ()
        | Proxy carrie -> check_abs carrie
        | Fn (_, body) -> check body
        | App (callee, args) -> check callee; Vector1.iter check args
        | Ov ov ->
            (match Env.get_implementation env ov with
            | Some (_, _, uv') -> check (Uv uv')
            | None -> ())
        | Uv uv' ->
            (match Env.get_uv env uv' with
            | Unassigned _ ->
                if uv = uv'
                then raise (Err.TypeError (pos, Occurs (uv, typ)))
                else ()
            | Assigned typ -> check typ)
        | Bv _ | Prim _ -> () in
    check typ

(* # Unification *)

and unify_abs : span -> Env.t -> T.abs -> T.abs -> T.coercion option matching
= fun pos env (Exists (existentials, body)) (Exists (existentials', body')) ->
    if Vector.length existentials = 0 && Vector.length existentials' = 0
    then unify pos env body body'
    else failwith "todo"

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
    | (Uv uv, typ') | (typ', Uv uv) ->
        (match Env.get_uv env uv with
        | Unassigned (_, kind, level) ->
            check_uv_assignee pos env uv level Int.max_int typ';
            Env.set_uv env uv (Assigned typ');
            {coercion = None; residual = empty}
        | Assigned _ -> failwith "unreachable: Assigned `typ` in `unify_whnf`")

    | (Values typs, _) -> (match typ' with
        | Values typs' ->
            if Vector.length typs = Vector.length typs' then begin
                let coercions = CCVector.create () in
                let (residual, noop) = Vector.fold2 (fun (residual, noop) typ typ' ->
                    let {coercion; residual = residual'} = unify pos env typ typ' in
                    CCVector.push coercions coercion;
                    (combine residual residual, noop && Option.is_none coercion)
                ) (empty, true) typs typs' in
                { coercion = if noop
                    then Some (ValuesCo (coercions |> CCVector.mapi (fun i -> function
                        | Some coercion -> coercion
                        | None -> T.Refl (Vector.get typs' i)
                    ) |> Vector.build))
                    else None
                ; residual }
            end else failwith "~ tuple lengths"
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (Pi (universals, domain, eff, codomain), _) -> (match typ' with
        | Pi (universals', domain', eff', codomain') -> failwith "TODO: unify Pi"
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (Record row, _) -> (match typ' with
        | Record row' ->
            let {coercion = row_coercion; residual} = unify pos env row row' in
            {coercion = Option.map (fun co -> T.RecordCo co) row_coercion; residual}
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (With _, _) -> (match typ' with
        | With {base = base'; label = label'; field = field'} ->
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
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (EmptyRow, _) -> (match typ' with
        | EmptyRow -> {coercion = None; residual = empty}
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (Proxy carrie, _) -> (match typ' with
        | Proxy carrie' -> 
            let {coercion; residual} = unify_abs pos env carrie carrie' in
            {coercion = Option.map (fun co -> T.ProxyCo co) coercion; residual}
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (T.App (callee, args), _) -> (match typ' with
        | T.App (callee', args') ->
            let {coercion = callee_co; residual} = unify_whnf pos env callee callee' in
            let matchings = Vector1.map2 (unify pos env) args args' in
            { coercion = (match callee_co with
                | Some callee_co ->
                    Some (Comp (callee_co, Vector1.map2 (fun {coercion; _} arg' -> match coercion with
                        | Some coercion -> coercion
                        | None -> T.Refl arg'
                    ) matchings args'))
                | None ->
                    if Vector1.exists (fun {coercion; _} -> Option.is_some coercion) matchings
                    then Some (Comp (Refl callee', Vector1.map2 (fun {coercion; _} arg' -> match coercion with
                        | Some coercion -> coercion
                        | None -> T.Refl arg'
                    ) matchings args'))
                    else None)
            ; residual = Vector1.fold (fun residual {coercion = _; residual = residual'} ->
                    combine residual residual'
                ) residual matchings }
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (Ov ov, _) -> (match typ' with
        | Ov ov'->
            if ov = ov'
            then {coercion = None; residual = empty}
            else raise (Err.TypeError (pos, Unify (typ, typ')))
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (Prim pt, _) -> (match typ' with
        | Prim pt' when Prim.eq pt pt'-> {coercion = None; residual = empty}
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (Fn _, _) -> failwith "unreachable: Fn in unify_whnf"
    | (Bv _, _) -> failwith "unreachable: Bv in unify_whnf"

(* Monotype check, occurs check, ov escape check, HKT capturability check and uv level updates.
   Complected for speed. *)
and check_uv_assignee pos env uv level max_uv_level typ =
    let rec check_abs (Exists (existentials, body) as typ : T.abs) =
        if Vector.length existentials = 0
        then check body
        else raise (Err.TypeError (pos, Polytype typ))

    and check = function
        | Values typs -> Vector.iter check typs
        | Pi (universals, domain, eff, codomain) ->
            if Vector.length universals = 0
            then begin
                Vector.iter check domain;
                check eff;
                check_abs codomain
            end else raise (Err.TypeError (pos, Polytype (T.to_abs typ)))
        | Record row -> check row
        | With {base; label = _; field} -> check base; check field
        | EmptyRow -> ()
        | Proxy carrie -> check_abs carrie
        | Fn (_, body) -> check body
        | App (callee, args) -> check callee; Vector1.iter check args
        | Ov ((_, level') as ov) ->
            (match Env.get_implementation env ov with
            | Some (_, _, uv') -> check (Uv uv')
            | None ->
                if level' <= level
                then ()
                else raise (Err.TypeError (pos, Escape ov)))
        | Uv uv' ->
            (match Env.get_uv env uv' with
            | Unassigned (name, kind, level') ->
                if uv = uv'
                then raise (Err.TypeError (pos, Occurs (uv, typ)))
                else if level' <= level
                then ()
                else if level' <= max_uv_level
                then Env.set_uv env uv' (Unassigned (name, kind, level)) (* hoist *)
                else raise (Err.TypeError (pos, IncompleteImpl (uv, uv')))
            | Assigned typ -> check typ)
        | Bv _ | Prim _ -> () in
    check typ

(* # Constraint Solving *)

and solve pos env residual =
    let open Residual in
    let rec solve env = function
        | Axioms (axiom_bindings, residual) ->
            let env = Env.push_axioms env axiom_bindings in
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
    | Some residual -> raise (Err.TypeError (pos, Unsolvable residual)))

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

