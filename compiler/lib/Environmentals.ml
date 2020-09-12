module T = Fc.Type
module Uv = Fc.Uv

type subst = Fc.Uv.subst

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
    | Bv {depth = depth'; sibli} as typ ->
        if depth' = depth
        then Vector.get substitution sibli
        else typ
    | Uv uv as typ ->
        (match Env.get_uv env uv with
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
    | Ov ((name, _), _) as path ->
        Name.Map.find_opt name substitution
            |> Option.fold ~some: (fun sibli -> Bv {depth; sibli}) ~none: path
    | Uv uv as typ ->
        (match Env.get_uv env uv with
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
    let params' = Vector.map (fun kind -> Env.generate env (Name.fresh (), kind)) params in
    let substitution = Vector.map (fun ov -> T.Ov ov) params' in
    (params', expose env substitution body)

let push_abs_skolems env (T.Exists (existentials, body)) =
    let (env, skolems) = Env.push_skolems env existentials in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    (env, skolems, expose env substitution body)

let push_arrow_skolems env universals domain eff codomain =
    let (env, skolems) = Env.push_skolems env universals in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    ( env, skolems
    , Vector.map (expose env substitution) domain
    , expose env substitution eff
    , expose_abs env substitution codomain )

let instantiate_abs env (T.Exists (existentials, body)) =
    let uvs = Vector.map (fun kind -> Env.uv env kind (Name.fresh ())) existentials in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    (uvs, expose env substitution body)

let instantiate_arrow env universals domain eff codomain =
    let uvs = Vector.map (fun kind -> Env.uv env kind (Name.fresh())) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , Vector.map (expose env substitution) domain
    , eff
    , expose_abs env substitution codomain )

