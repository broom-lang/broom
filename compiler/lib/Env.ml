module TS = TyperSigs

module Make (C : TS.TYPING) : TS.ENV = struct

module T = Fc.Type
module Uv = Fc.Uv

module Bindings = Map.Make(Name)

type uv = Fc.Uv.t
type subst = Fc.Uv.subst

let ref = TxRef.ref
let (!) = TxRef.(!)

type scope =
    | Hoisting of T.ov list TxRef.rref * T.level
    | Rigid of T.ov Vector.t
    | Val of Name.t * T.t
    | Axiom of (Name.t * T.ov * uv) Name.Map.t

type t =
    { tx_log : Fc.Uv.subst
    ; scopes : scope list
    ; level : Fc.Type.level }

let initial_level = 1

let interactive () =
    { tx_log = Fc.Uv.new_subst ()
    ; scopes = [Hoisting (ref [], initial_level)]
    ; level = initial_level }

let eval () =
    { tx_log = Fc.Uv.new_subst ()
    ; scopes = [Hoisting (ref [], initial_level)]
    ; level = initial_level }

let find (env : t) pos name =
    let rec find = function
        | Val (name', typ) :: scopes -> if name' = name then typ else find scopes
        | (Hoisting _ | Rigid _ | Axiom _) ::scopes -> find scopes
        | [] -> raise (TypeError.TypeError (pos, Unbound name)) in
    find env.scopes

let push_val (env : t) name typ =
    {env with scopes = Val (name, typ) :: env.scopes}

let push_existential (env : t) =
    let bindings = ref [] in
    let level = env.level + 1 in
    ( {env with scopes = Hoisting (bindings, level) :: env.scopes; level}
    , bindings )

let push_skolems (env : t) kinds =
    let level = env.level + 1 in
    let ebs = Vector.map (fun kind -> (Name.fresh (), kind)) kinds in
    let skolems = Vector.map (fun binding -> (binding, level)) ebs in
    ( {env with scopes = Rigid skolems :: env.scopes; level}
    , skolems )

let push_axioms (env : t) axioms =
    let bindings = Vector1.fold (fun bindings ((_, ((k, _), _), _) as v) ->
        Name.Map.add k v bindings
    ) Name.Map.empty axioms in
    {env with scopes = Axiom bindings :: env.scopes}

let generate env binding =
    let rec generate = function
        | Hoisting (bindings, level) :: _ ->
            let ov = (binding, level) in
            TxRef.set env.tx_log bindings (ov :: !bindings);
            ov
        | _ :: scopes' -> generate scopes'
        | [] -> failwith "Typer.generate: missing root Hoisting scope"
    in generate env.scopes

let get_implementation (env : t) (((name, _), _) : T.ov) =
    let rec get = function
        | Axiom kvs :: scopes ->
            (match Name.Map.find_opt name kvs with
            | Some axiom -> Some axiom
            | None -> get scopes)
        | _ :: scopes -> get scopes
        | [] -> None
    in get env.scopes

let uv (env : t) kind name = Fc.Uv.make env.tx_log (Unassigned (name, kind, env.level))

let get_uv (env : t) uv = Fc.Uv.get env.tx_log uv

let set_uv (env : t) uv v = Fc.Uv.set env.tx_log uv v

let sibling (env : t) kind uv = match get_uv env uv with
    | Unassigned (_, _, level) -> Fc.Uv.make env.tx_log (Unassigned (Name.fresh (), kind, level))
    | Assigned _ -> failwith "unreachable"

let set_expr (env : t) ref expr = TxRef.set env.tx_log ref expr
let set_coercion (env : t) ref coercion = TxRef.set env.tx_log ref coercion

let document (env : t) to_doc v = to_doc env.tx_log v

let rec expose_abs' env depth substitution (Exists (params, body) : T.abs) : T.abs =
    let depth = depth + 1 in
    Exists (params, expose' env depth substitution body)

and expose' env depth substitution = function
    | Values typs -> Values (Vector.map (expose' env depth substitution) typs)
    | Pi (params, domain, eff, codomain) ->
        let depth = depth + 1 in
        Pi ( params, Vector.map (expose' env depth substitution) domain, eff
            , expose_abs' env depth substitution codomain )
    | Record row -> Record (expose' env depth substitution row)
    | With {base; label; field} ->
        With {base = expose' env depth substitution base; label; field = expose' env depth substitution field}
    | EmptyRow -> EmptyRow
    | Proxy typ -> Proxy (expose_abs' env depth substitution typ)
    | Fn (params, body) -> Fn (params, expose' env (depth + 1) substitution body)
    | App (callee, args) ->
        let args = Vector1.map (expose' env depth substitution) args in
        (match expose' env depth substitution callee with
        | App (callee, args') -> App (callee, Vector1.append args' args) (* TODO: is this sufficient? *)
        | callee -> App (callee, args))
    | Bv {depth = depth'; sibli; kind = _} as typ ->
        if depth' = depth
        then Vector.get substitution sibli
        else typ
    | Uv uv as typ ->
        (match get_uv env uv with
        | Assigned typ -> expose' env depth substitution typ
        | Unassigned _ -> typ)
    | (Ov _ | Prim _) as typ -> typ

and expose_template' env depth substitution = function
    | T.PiL (arity, codomain) -> T.PiL (arity, expose_template' env depth substitution codomain)
    | WithL {base; label; field} ->
        WithL { base = expose_template' env depth substitution base
              ; label; field = expose_template' env depth substitution field }
    | ProxyL path -> ProxyL (expose' env depth substitution path)
    | Hole -> Hole

let expose_abs env = expose_abs' env 0
let expose env = expose' env 0
let expose_template env = expose_template' env 0

(* --- *)

let rec close_abs' env depth substitution (Exists (params, body) : T.abs) : T.abs =
    let depth = depth + 1 in
    Exists (params, close' env depth substitution body)

and close' env depth substitution = function
    | Values typs -> Values (Vector.map (close' env depth substitution) typs)
    | Pi (params, domain, eff, codomain) ->
        let depth = depth + 1 in
        Pi ( params, Vector.map (close' env depth substitution) domain, eff
            , close_abs' env depth substitution codomain )
    | Record row -> Record (close' env depth substitution row)
    | With {base; label; field} ->
        With {base = close' env depth substitution base; label; field = close' env depth substitution field}
    | EmptyRow -> EmptyRow
    | Proxy typ -> Proxy (close_abs' env depth substitution typ)
    | Fn (params, body) -> Fn (params, close' env (depth + 1) substitution body)
    | App (callee, args) ->
        let args = Vector1.map (close' env depth substitution) args in
        (match close' env depth substitution callee with
        | App (callee, args') -> App (callee, Vector1.append args' args) (* TODO: is this sufficient? *)
        | callee -> App (callee, args))
    | Ov ((name, kind), _) as path ->
        Name.Map.find_opt name substitution
            |> Option.fold ~some: (fun sibli -> Bv {depth; sibli; kind}) ~none: path
    | Uv uv as typ ->
        (match get_uv env uv with
        | Assigned typ -> close' env depth substitution typ
        | Unassigned _ -> typ)
    | (Bv _ | Prim _) as typ -> typ

and close_template' env depth substitution = function
    | T.PiL (arity, codomain) -> T.PiL (arity, close_template' env depth substitution codomain)
    | WithL {base; label; field} ->
        WithL { base = close_template' env depth substitution base
              ; label; field = close_template' env depth substitution field }
    | ProxyL path -> ProxyL (close' env depth substitution path)
    | Hole -> Hole

let close env = close' env 0
let close_template env = close_template' env 0
let close_abs env = close_abs' env 0

(* --- *)

let reabstract env (T.Exists (params, body)) =
    let params' = Vector.map (fun kind -> generate env (Name.fresh (), kind)) params in
    let substitution = Vector.map (fun ov -> T.Ov ov) params' in
    (params', expose env substitution body)

let push_abs_skolems env (T.Exists (existentials, body)) =
    let (env, skolems) = push_skolems env existentials in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    (env, skolems, expose env substitution body)

let push_arrow_skolems env universals domain eff codomain =
    let (env, skolems) = push_skolems env universals in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    ( env, skolems
    , Vector.map (expose env substitution) domain
    , expose env substitution eff
    , expose_abs env substitution codomain )

let instantiate_abs env (T.Exists (existentials, body)) =
    let uvs = Vector.map (fun kind -> uv env kind (Name.fresh ())) existentials in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    (uvs, expose env substitution body)

let instantiate_arrow env universals domain eff codomain =
    let uvs = Vector.map (fun kind -> uv env kind (Name.fresh())) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , Vector.map (expose env substitution) domain
    , eff
    , expose_abs env substitution codomain )

end

