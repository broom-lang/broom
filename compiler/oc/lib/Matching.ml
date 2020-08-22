module ResidualMonoid = struct
    include Monoid.OfSemigroup(Residual)

    let skolemized skolems m = Option.map (fun r -> Residual.Skolems (skolems, r)) m
end

module Make (E : TyperSigs.ELABORATION) : TyperSigs.MATCHING = struct

module T = Fc.Type
open T
open Residual
open TypeError

type 'a matching = {coercion : 'a; residual : Residual.t option}

let focalize _ = failwith "TODO"

(* # Unification *)

let rec unify_abs pos env (Exists (existentials, locator, body)) (Exists (existentials', locator', body')) =
    if Vector.length existentials = 0 && Vector.length existentials' = 0
    then unify pos env body body'
    else failwith "todo"

and unify pos env typ typ' : coercion option matching =
    let (>>=) = Option.bind in
    let res =
        E.eval env typ >>= fun (typ, co) ->
        E.eval env typ' |> Option.map (fun (typ', co'') ->
        let {coercion = co'; residual} = unify_eval pos env typ typ' in
        { coercion =
            (match (co, co', co'') with
            | (Some co, Some co', Some co'') -> Some (Trans (Trans (co, co'), Symm co''))
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
        let patchable = ref (Refl typ') in
        { coercion = Some (T.Patchable patchable)
        ; residual = Some (Unify (typ, typ', patchable)) }

and unify_eval pos env (typ : typ) (typ' : typ) : coercion option matching =
    let open ResidualMonoid in
    match (typ, typ') with
    | (Uv uv, typ') | (typ', Uv uv) ->
        (match Env.get_uv env uv with
        | Unassigned (_, level) ->
            check_uv_assignee pos env uv level Int.max_int typ';
            Env.set_uv env uv (Assigned typ');
            {coercion = None; residual = empty}
        | Assigned _ -> failwith "unreachable: Assigned `typ` in `unify_eval`")

    | (Type carrie, _) -> (match typ' with
        | Type carrie' -> 
            let {coercion; residual} = unify_abs pos env carrie carrie' in
            { coercion =
                (match coercion with
                | Some co -> Some (TypeCo co)
                | None -> None)
            ; residual }
        | _ -> raise (TypeError (pos, Unify (typ, typ'))))

    | (T.App (callee, args), _) -> (match typ' with
        | T.App (callee', args') ->
            let {coercion = callee_co; residual} = unify_eval pos env callee callee' in
            let matchings = Vector1.map2 (unify pos env) args args' in
            { coercion = (match callee_co with
                | Some callee_co ->
                    Some (Comp (callee_co, Vector1.map2 (fun {coercion; _} arg' -> match coercion with
                        | Some coercion -> coercion
                        | None -> Refl arg'
                    ) matchings args'))
                | None ->
                    if Vector1.exists (fun {coercion; _} -> Option.is_some coercion) matchings
                    then Some (Comp (Refl callee', Vector1.map2 (fun {coercion; _} arg' -> match coercion with
                        | Some coercion -> coercion
                        | None -> Refl arg'
                    ) matchings args'))
                    else None)
            ; residual = Vector1.fold_left (fun residual {coercion = _; residual = residual'} ->
                    combine residual residual'
                ) residual matchings }
        | _ -> raise (TypeError (pos, Unify (typ, typ'))))

    | (Ov ov, _) -> (match typ' with
        | Ov ov'->
            if ov = ov'
            then {coercion = None; residual = empty}
            else raise (TypeError (pos, Unify (typ, typ')))
        | _ -> raise (TypeError (pos, Unify (typ, typ'))))

    | (Prim pt, _) -> (match typ' with
        | Prim pt' when Prim.eq pt pt'-> {coercion = None; residual = empty}
        | _ -> raise (TypeError (pos, Unify (typ, typ'))))

    | (Fn _, _) -> failwith "unreachable: Fn in unify_eval"
    | (Bv _, _) -> failwith "unreachable: Bv in unify_eval"
    | (Use _, _) -> failwith "unreachable: Use in unify_eval"

(* Monotype check, occurs check, ov escape check, HKT capturability check and uv level updates.
   Complected for speed. *)
and check_uv_assignee pos env uv level max_uv_level typ =
    let rec check_abs (Exists (existentials, _, body) as typ) =
        if Vector.length existentials = 0
        then check body
        else raise (TypeError (pos, Polytype typ))

    and check = function
        | Pi (universals, domain, eff, codomain) ->
            if Vector.length universals = 0
            then begin
                Vector.iter (fun (_, dom) -> check dom) domain;
                check eff;
                check_abs codomain
            end else raise (TypeError (pos, Polytype (to_abs typ)))
        | Record fields -> Vector.iter (fun {label = _; typ} -> check typ) fields
        | Type carrie -> check_abs carrie
        | Fn body -> check body
        | App (callee, args) -> check callee; Vector1.iter check args
        (*| Ov ((_, level') as ov) ->
            (match Env.get_implementation env ov with
            | Some (_, _, uv') -> check (Uv uv')
            | None ->
                if level' <= level
                then ()
                else raise (TypeError (pos, Escape ov)))*)
        | Uv uv' ->
            (match Env.get_uv env uv' with
            | Unassigned (name, level') ->
                if uv = uv'
                then raise (TypeError (pos, Occurs (uv, typ)))
                else if level' <= level
                then ()
                else if level' <= max_uv_level
                then Env.set_uv env uv' (Unassigned (name, level)) (* hoist *)
                else raise (TypeError (pos, IncompleteImpl (uv, uv')))
            | Assigned typ -> check typ)
        | Bv _ | Use _ | Prim _ -> () in
    check typ

(* # Constraint Solving *)

and solve pos env residual =
    let rec solve env = function
        (*| Axioms (axiom_bindings, residual) ->
            let env = Env.push_axioms env axiom_bindings in
            solve env residual*)

        (*| Skolems (skolems, residual) ->
            let env = Env.push_skolems env skolems in
            solve env residual*)

        | Residuals (residual, residual') ->
            ResidualMonoid.combine (solve env residual) (solve env residual')

        (*| Sub (typ, locator, super, patchable) ->
            let {coercion = Cf coerce; residual} = subtype pos env typ locator super in
            patchable := coerce (!patchable);
            residual*)

        | Unify (typ, typ', patchable) ->
            let {coercion; residual} = unify pos env typ typ' in
            Option.iter (fun coercion -> patchable := coercion) coercion;
            residual
    in
    (match Option.bind residual (solve env) with
    | None -> ()
    | Some residual -> raise (TypeError (pos, Unsolvable residual)))

(* Public API *)

let solving_coercion pos env typ super = failwith "TODO"

let solving_subtype pos env typ locator super = failwith "TODO"

let solving_unify pos env typ super =
    let {coercion; residual} = unify pos env typ super in
    solve pos env residual;
    coercion

end

