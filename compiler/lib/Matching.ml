module ResidualMonoid = struct
    include Monoid.OfSemigroup(Residual)

    let skolemized skolems m = Option.map (fun r -> Residual.Skolems (skolems, r)) m
end

module Make (Elab : TyperSigs.ELABORATION) : TyperSigs.MATCHING = struct

module T = Fc.Type
module E = Fc.Term.Expr
module Err = TypeError

type span = Util.span
type coercer = TyperSigs.coercer

type 'a matching = {coercion : 'a; residual : Residual.t option}

let ref = TxRef.ref
let (!) = TxRef.(!)
let sibling = Env.sibling

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
                                  , Vector.init arity (fun _ -> (T.Hole, T.Uv (sibling env uv)))
                                  , Uv (sibling env uv), T.to_abs (Uv (sibling env uv)) ))
                    | TypeL _ -> (uv, T.Type (T.to_abs (Uv (sibling env uv))))
                    | RecordL row_template -> (uv, Record (Uv (sibling env uv)))
                    | WithL {base = _; label; field = _} ->
                        (uv, (With {base = Uv (sibling env uv); label; field = Uv (sibling env uv)}))
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
            | TypeL _ ->
                (match typ with
                | Type _ -> (Cf Fun.id, typ)
                | _ -> raise (Err.TypeError (pos, Unusable (template, typ))))
            | RecordL _ ->
                (match typ with
                | Record _ -> (Cf Fun.id, typ)
                | _ -> raise (Err.TypeError (pos, Unusable (template, typ))))
            | WithL {base = _; label; field = _} ->
                (match typ with
                | With {base; label = label'; field = field'} ->
                    if label' = label
                    then (Cf Fun.id, typ)
                    else begin
                        let (coercion, typ) = focalize pos env base template in
                        match typ with
                        | With {base; label = _; field} ->
                            let base = T.With {base; label = label'; field = field'} in
                            (coercion, With {base; label; field})
                        | _ -> failwith "unreachable: WithL focalization produced non-With."
                    end
                | _ -> raise (Err.TypeError (pos, Unusable (template, typ))))
            | Hole -> failwith "unreachable: Hole as template in `focalize`.") in

    match Elab.eval env typ with
    | Some (typ, coercion) ->
        let (Cf cf as coercer, typ) = focalize_whnf typ in
        ( (match coercion with
          | Some coercion -> TyperSigs.Cf (fun v -> cf {pos; v = Cast (v, coercion)})
          | None -> coercer)
        , typ )
    | None -> failwith "unreachable: `whnf` failed in `focalize`."

and focalize_locator : T.locator -> T.t -> T.locator 
= fun locator -> function
    | T.Pi (_, domain, _, _) ->
        (match locator with
        | PiL _ -> locator
        | Hole -> PiL (Vector.length domain, Hole)
        | _ -> failwith "unreachable: `Pi` locator")
    | Record _ ->
        (match locator with
        | RecordL _ -> locator
        | Hole -> RecordL Hole
        | _ -> failwith "unreachable: `Record` locator")
    | With {base = _; label; field = _} ->
        (match locator with
        | WithL {base = _; label = locator_label; field = _} when locator_label = label ->
            locator
        | Hole -> WithL {base = Hole; label; field = Hole}
        | _ -> failwith "unreachable: `With` locator")
    | Type _ ->
        (match locator with
        | TypeL _ -> locator
        | Hole -> TypeL (Prim Int) (* HACK *)
        | _ -> failwith "unreachable: `Type` locator")
    | _ -> locator (* HACK? *)

(* # Subtyping *)

let rec coercion : span -> bool -> Env.t -> T.t -> T.ov Vector.t * T.locator * T.t -> coercer matching
= fun pos occ env typ (existentials, super_locator, super) ->
    match Vector1.of_vector existentials with
    | Some existentials ->
        let axiom_bindings = Vector1.map (fun (((name, _), _) as param) ->
            (Name.fresh (), param, Env.uv env name)
        ) existentials in
        let env = Env.push_axioms env axiom_bindings in
        let {coercion = Cf coerce; residual} = subtype pos occ env typ super_locator super in

        let axioms = Vector1.map (fun (axname, (((_, kind), _) as ov), impl) -> match kind with
            | T.ArrowK (domain, _) ->
                let args = Vector1.mapi (fun sibli _ -> T.Bv {depth = 0; sibli}) domain in
                ( axname, Vector1.to_vector domain
                , T.App (Ov ov, args), T.App (Uv impl, args) )
            | TypeK -> (axname, Vector.of_list [], Ov ov, Uv impl)
        ) axiom_bindings in
        { coercion = Cf (fun v -> {pos; v = Axiom (axioms, coerce v)})
        ; residual = Option.map (fun residual -> Residual.Axioms (axiom_bindings, residual)) residual }
    | None -> subtype pos occ env typ super_locator super

and subtype_abs : span -> bool -> Env.t -> T.abs -> T.locator -> T.abs -> coercer matching
= fun pos occ env typ locator super ->
    let (env, skolems, typ) = Environmentals.push_abs_skolems env typ in
    let (uvs, super_locator, super) = Environmentals.instantiate_abs env super in
    match Vector1.of_vector skolems with
    | Some skolems ->
        let skolems = Vector1.map fst skolems in
        (match Vector1.of_vector uvs with
        | Some uvs ->
            let {coercion = Cf coerce; residual} = subtype pos occ env typ super_locator super in

            let name = Name.fresh () in
            let impl = {E.name; typ} in
            let uvs = Vector1.map (fun uv -> T.Uv uv) uvs in
            let body = {Util.pos; v = E.Pack (uvs, coerce {Util.pos; v = Use name})} in
            { coercion = Cf (fun v -> {pos; v = Unpack (skolems, impl, v, body)})
            ; residual = ResidualMonoid.skolemized (Vector1.map snd skolems) residual }
        | None ->
            let {coercion = Cf coerce; residual} = subtype pos occ env typ locator super in

            let name = Name.fresh () in 
            let impl = {E.name; typ} in
            let body = coerce {Util.pos; v = Use name} in
            { coercion = Cf (fun v -> {pos; v = Unpack (skolems, impl, v, body)})
            ; residual = ResidualMonoid.skolemized (Vector1.map snd skolems) residual })

    | None ->
        (match Vector1.of_vector uvs with
        | Some uvs ->
            let {coercion = Cf coerce; residual} = subtype pos occ env typ super_locator super in

            let uvs = Vector1.map (fun uv -> T.Uv uv) uvs in
            {coercion = Cf (fun v -> {pos; v = Pack (uvs, coerce v)}); residual}
        | None -> subtype pos occ env typ locator super)

and subtype : span -> bool -> Env.t -> T.t -> T.locator -> T.t -> coercer matching
= fun pos occ env typ locator super ->
    let empty = ResidualMonoid.empty in
    let combine = ResidualMonoid.combine in

    let articulate pos occ env uv_typ template = match uv_typ with
        | T.Uv uv ->
            (match Env.get_uv env uv with
            | Unassigned (_, level) ->
                let (uv, typ) = match template with
                    | T.Uv uv' ->
                        (match Env.get_uv env uv' with
                        | Unassigned (_, level') ->
                            if level' <= level
                            then (uv, template)
                            else (uv', uv_typ)
                        | Assigned _ -> failwith "unreachable: Assigned as template of `articulate`")

                    | Ov ((_, level') as ov) ->
                        if level' <= level
                        then (uv, Ov ov)
                        else raise (Err.TypeError (pos, Escape ov))

                    | Pi (_, domain, _, _) ->
                        (uv, Pi ( Vector.of_list []
                                , Vector.map (fun _ -> (T.Hole, T.Uv (sibling env uv))) domain
                                , Uv (sibling env uv)
                                , T.to_abs (Uv (sibling env uv)) ))
                    | Record _ -> (uv, Record (Uv (sibling env uv)))
                    | With {base = _; label; field = _} ->
                        (uv, With {base = Uv (sibling env uv); label; field = Uv (sibling env uv)})
                    | EmptyRow -> (uv, EmptyRow)
                    | Type _ -> (uv, Type (T.to_abs (Uv (sibling env uv))))
                    | App (_, args) ->
                        (uv, T.App (Uv (sibling env uv), Vector1.map (fun _ -> T.Uv (sibling env uv)) args))
                    | Prim pt -> (uv, Prim pt)

                    | Fn _ -> failwith "unreachable: `Fn` as template of `articulate`"
                    | Bv _ -> failwith "unreachable: `Bv` as template of `articulate`"
                    | Use _ -> failwith "unreachable: `Use` as template of `articulate`" in
                Env.set_uv env uv (Assigned typ);
                typ
            | Assigned _ -> failwith "unreachable: `articulate` on assigned uv")
        | _ -> failwith "unreachable: `articulate` on non-uv" in

    let subtype_whnf : bool -> T.t -> T.locator -> T.t -> coercer matching
    = fun occ typ locator super -> match (typ, super) with
        | (Uv uv, Uv uv') when uv = uv' -> {coercion = Cf Fun.id; residual = None}
        | (Uv uv, _) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                if occ then occurs_check pos env uv super else ();
                subtype pos false env (articulate pos occ env typ super) locator super
            | Assigned _ -> failwith "unreachable: Assigned `typ` in `subtype_whnf`")
        | (_, Uv uv) ->
            (match Env.get_uv env uv with
            | Unassigned _ ->
                if occ then occurs_check pos env uv typ else ();
                subtype pos false env typ locator (articulate pos occ env super typ)
            | Assigned _ -> failwith "unreachable: Assigned `super` in `subtype_whnf`")

        | (Pi (universals, domain, eff, codomain), _) -> (match super with
            | Pi (universals', domain', eff', codomain') ->
                let codomain_locator = match locator with
                    | PiL (_, codomain_locator) -> codomain_locator
                    | _ -> failwith "unreachable: function locator" in
                let (env, universals', domain', eff', codomain_locator, codomain') =
                    Environmentals.push_arrow_skolems env universals'
                        domain' eff' codomain_locator codomain' in
                let (uvs, domain, eff, codomain) =
                    Environmentals.instantiate_arrow env universals domain eff codomain in

                (* FIXME: raises on arity mismatch: *)
                let {coercion = domain_coercions; residual = domain_residual} =
                    Vector.fold2 (fun {coercion = coercions; residual} (loc, domain) (_, domain') ->
                        let {coercion; residual = residual'} = subtype pos occ env domain' loc domain in
                        {coercion = coercion :: coercions; residual = combine residual residual'})
                    {coercion = []; residual = empty} domain domain' in
                let domain_coercions = domain_coercions |> List.rev |> Vector.of_list in
                let {coercion = _; residual = eff_residual} = subtype pos occ env eff Hole eff' in
                let {coercion = Cf coerce_codomain; residual = codomain_residual} =
                    subtype_abs pos occ env codomain codomain_locator codomain' in

                let names = Vector.map (fun _ -> Name.fresh ()) domain in
                let params = Vector.map2 (fun name (_, domain') -> {E.name; typ = domain'})
                    names domain' in
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
                let row_locator = match locator with
                    | RecordL row_locator -> row_locator
                    | _ -> failwith "unreachable: record locator" in
                subtype pos occ env row row_locator super_row (* FIXME *)
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

        | (With {base; label; field}, _) -> (match super with
            | With {base = super_base; label = super_label; field = super_field} ->
                let (base_locator, field_locator) = match locator with
                    | WithL {base; label = locator_label; field} when locator_label = super_label ->
                        (base, field)
                    | _ -> failwith "unreachable: record locator" in
                if label = super_label then begin
                    let {coercion = _; residual = base_residual} =
                        subtype pos occ env base base_locator super_base in
                    let {coercion = _; residual = field_residual} =
                        subtype pos occ env field field_locator super_field in
                    { coercion = Cf Fun.id (* NOTE: Row types have no values so this will not get used *)
                    ; residual = combine base_residual field_residual }
                end else failwith "TODO: subtype With label flipping"
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

        | (EmptyRow, _) -> (match super with
            | EmptyRow -> {coercion = Cf Fun.id; residual = empty}
            | _ -> raise (Err.TypeError (pos, SubType (typ, super))))

        | (Type (Exists (existentials, _, carrie) as abs_carrie), _) -> (match super with
            | Type abs_carrie' ->
                (match locator with
                | TypeL (App (callee, args)) ->
                    (match Elab.eval env callee with
                    (*| Some (Uv ({contents = Unassigned (_, level)} as uv), _) ->
                        if Vector.length existentials = 0 then begin
                            let (_, substitution) = Vector1.fold_left (fun (i, substitution) arg ->
                                match arg with
                                | Ov ((name, _), _) -> (i + 1, Name.Map.add name i substitution)
                                | _ -> failwith "unreachable: non-ov path arg in path locator"
                            ) (0, Name.Map.empty) args in
                            let impl = T.Fn (close substitution carrie) in
                            let max_uv_level = match Vector1.get args 0 with
                                | Ov (_, level') -> level' - 1
                                | _ -> failwith "unreachable: non-ov path arg in path locator" in
                            check_uv_assignee pos env uv level max_uv_level impl;
                            uv := Assigned impl;
                            { coercion = TyperSigs.Cf (fun _ -> {v = Proxy abs_carrie'; pos})
                            ; residual = empty }
                        end else raise (TypeError (pos, Polytype abs_carrie))*)

                    | _ -> (* TODO: Use unification (?) *)
                        let {coercion = _; residual} =
                            subtype_abs pos occ env abs_carrie Hole abs_carrie' in
                        let {coercion = _; residual = residual'} =
                            subtype_abs pos occ env abs_carrie' Hole abs_carrie in
                        { coercion = Cf (fun _ -> {v = Proxy abs_carrie'; pos})
                        ; residual = combine residual residual' })

                | TypeL _ -> (* TODO: Use unification (?) *)
                    let {coercion = _; residual} =
                        subtype_abs pos occ env abs_carrie Hole abs_carrie' in
                    let {coercion = _; residual = residual'} =
                        subtype_abs pos occ env abs_carrie' Hole abs_carrie in
                    { coercion = Cf (fun _ -> {v = Proxy abs_carrie'; pos})
                    ; residual = combine residual residual' }

                | _ -> failwith "unreachable: `Type` locator")
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
        | (Bv _, _) -> failwith "unreachable: Bv in subtype_whnf"
        | (Use _, _) -> failwith "unreachable: Use in subtype_whnf" in

    let (>>=) = Option.bind in
    let res =
        Elab.eval env typ >>= fun (typ', co) ->
        Elab.eval env super |> Option.map (fun (super', co') ->
            let locator = focalize_locator locator super' in
            let {coercion = Cf coerce; residual} = subtype_whnf occ typ' locator super' in
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
            TxRef.set (Env.tx_log env) patchable v;
            {pos; v = Patchable patchable})
        ; residual = Some (Sub (occ, typ, locator, super, patchable)) }

and occurs_check pos env uv typ =
    let rec check_abs (Exists (_, _, body) : T.abs) = check body

    and check = function
        | Pi (_, domain, eff, codomain) ->
            Vector.iter (fun (_, dom) -> check dom) domain;
            check eff;
            check_abs codomain
        | Record row -> check row
        | With {base; label = _; field} -> check base; check field
        | EmptyRow -> ()
        | Type carrie -> check_abs carrie
        | Fn body -> check body
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
        | Bv _ | Use _ | Prim _ -> () in
    check typ

(* # Unification *)

and unify_abs : span -> Env.t -> T.abs -> T.abs -> T.coercion option matching
= fun pos env (Exists (existentials, locator, body)) (Exists (existentials', locator', body')) ->
    if Vector.length existentials = 0 && Vector.length existentials' = 0
    then unify pos env body body'
    else failwith "todo"

and unify pos env typ typ' : T.coercion option matching =
    let (>>=) = Option.bind in
    let res =
        Elab.eval env typ >>= fun (typ, co) ->
        Elab.eval env typ' |> Option.map (fun (typ', co'') ->
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
        | Unassigned (_, level) ->
            check_uv_assignee pos env uv level Int.max_int typ';
            Env.set_uv env uv (Assigned typ');
            {coercion = None; residual = empty}
        | Assigned _ -> failwith "unreachable: Assigned `typ` in `unify_whnf`")

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
            let rec pull typ = match Elab.eval env typ with
                | Some (With {base; label; field}, eval_co) ->
                    if label = label'
                    then (base, field)
                    else begin
                        let (base, field'') = pull base in
                        (With {base; label; field}, field'')
                    end in
            let (base, field) = pull typ in
            let {coercion = base_co; residual = base_residual} = unify pos env base base' in
            let {coercion = field_co; residual = field_residual} = unify pos env field field' in
            { coercion = (match (base_co, field_co) with
                | (Some base, Some field) -> Some (WithCo {base; label = label'; field})
                | (Some base, None) -> Some (WithCo {base; label = label'; field = Refl field'})
                | (None, Some field) -> Some (WithCo {base = Refl base'; label = label'; field})
                | (None, None) -> None)
            ; residual = combine base_residual field_residual }
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (EmptyRow, _) -> (match typ' with
        | EmptyRow -> {coercion = None; residual = empty}
        | _ -> raise (Err.TypeError (pos, Unify (typ, typ'))))

    | (Type carrie, _) -> (match typ' with
        | Type carrie' -> 
            let {coercion; residual} = unify_abs pos env carrie carrie' in
            {coercion = Option.map (fun co -> T.TypeCo co) coercion; residual}
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
    | (Use _, _) -> failwith "unreachable: Use in unify_whnf"

(* Monotype check, occurs check, ov escape check, HKT capturability check and uv level updates.
   Complected for speed. *)
and check_uv_assignee pos env uv level max_uv_level typ =
    let rec check_abs (Exists (existentials, _, body) as typ : T.abs) =
        if Vector.length existentials = 0
        then check body
        else raise (Err.TypeError (pos, Polytype typ))

    and check = function
        | Pi (universals, domain, eff, codomain) ->
            if Vector.length universals = 0
            then begin
                Vector.iter (fun (_, dom) -> check dom) domain;
                check eff;
                check_abs codomain
            end else raise (Err.TypeError (pos, Polytype (T.to_abs typ)))
        | Record row -> check row
        | With {base; label = _; field} -> check base; check field
        | EmptyRow -> ()
        | Type carrie -> check_abs carrie
        | Fn body -> check body
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
            | Unassigned (name, level') ->
                if uv = uv'
                then raise (Err.TypeError (pos, Occurs (uv, typ)))
                else if level' <= level
                then ()
                else if level' <= max_uv_level
                then Env.set_uv env uv' (Unassigned (name, level)) (* hoist *)
                else raise (Err.TypeError (pos, IncompleteImpl (uv, uv')))
            | Assigned typ -> check typ)
        | Bv _ | Use _ | Prim _ -> () in
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

        | Sub (occ, typ, locator, super, patchable) ->
            let {coercion = Cf coerce; residual} = subtype pos occ env typ locator super in
            TxRef.set (Env.tx_log env) patchable (coerce !patchable);
            residual

        | Unify (typ, typ', patchable) ->
            let {coercion; residual} = unify pos env typ typ' in
            Option.iter (fun coercion -> TxRef.set (Env.tx_log env) patchable coercion)
                coercion;
            residual
    in
    (match Option.bind residual (solve env) with
    | None -> ()
    | Some residual -> raise (Err.TypeError (pos, Unsolvable residual)))

(* Public API *)

let solving_coercion pos env typ super =
    let {coercion; residual} = coercion pos true env typ super in
    solve pos env residual;
    coercion

let solving_subtype pos env typ locator super =
    let {coercion; residual} = subtype pos true env typ locator super in
    solve pos env residual;
    coercion

let solving_unify pos env typ super =
    let {coercion; residual} = unify pos env typ super in
    solve pos env residual;
    coercion

end

