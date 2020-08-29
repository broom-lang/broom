module T = Fc.Type
module Uv = Fc.Uv

type subst = Fc.Uv.subst

let rec expose_abs' env depth substitution (Exists (params, locator, body) : T.abs) : T.abs =
    let depth = depth + 1 in
    Exists (params, expose_locator' env depth substitution locator, expose' env depth substitution body)

and expose' env depth substitution = function
    | Pi (params, domain, eff, codomain) ->
        let depth = depth + 1 in
        let expose_domain env (locator, domain) =
            (expose_locator' env depth substitution locator, expose' env depth substitution domain) in
        Pi (params, Vector.map (expose_domain env) domain, eff, expose_abs' env depth substitution codomain)
    | Record row -> Record (expose' env depth substitution row)
    | With {base; label; field} ->
        With {base = expose' env depth substitution base; label; field = expose' env depth substitution field}
    | EmptyRow -> EmptyRow
    | Type typ -> Type (expose_abs' env depth substitution typ)
    | Fn body -> Fn (expose' env (depth + 1) substitution body)
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
    | (Use _ | Ov _ | Prim _) as typ -> typ

and expose_locator' env depth substitution = function
    | PiL (arity, codomain) -> PiL (arity, expose_locator' env depth substitution codomain)
    | RecordL row -> RecordL (expose_locator' env depth substitution row)
    | WithL {base; label; field} ->
        WithL { base = expose_locator' env depth substitution base
              ; label; field = expose_locator' env depth substitution field }
    | TypeL path -> TypeL (expose' env depth substitution path)
    | Hole -> Hole

let expose_abs env = expose_abs' env 0
let expose env = expose' env 0
let expose_locator env = expose_locator' env 0

(* --- *)

let rec close_abs' env depth substitution (Exists (params, locator, body) : T.abs) : T.abs =
    let depth = depth + 1 in
    Exists (params, close_locator' env depth substitution locator, close' env depth substitution body)

and close' env depth substitution = function
    | Pi (params, domain, eff, codomain) ->
        let depth = depth + 1 in
        let close_domain env (locator, domain) =
            (close_locator' env depth substitution locator, close' env depth substitution domain) in
        Pi (params, Vector.map (close_domain env) domain, eff, close_abs' env depth substitution codomain)
    | Record row -> Record (close' env depth substitution row)
    | With {base; label; field} ->
        With {base = close' env depth substitution base; label; field = close' env depth substitution field}
    | EmptyRow -> EmptyRow
    | Type typ -> Type (close_abs' env depth substitution typ)
    | Fn body -> Fn (close' env (depth + 1) substitution body)
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
    | (Use _ | Bv _ | Prim _) as typ -> typ

and close_locator' env depth substitution = function
    | PiL (arity, codomain) -> PiL (arity, close_locator' env depth substitution codomain)
    | RecordL row -> RecordL (close_locator' env depth substitution row)
    | WithL {base; label; field} ->
        WithL { base = close_locator' env depth substitution base
              ; label; field = close_locator' env depth substitution field }
    | TypeL path -> TypeL (close' env depth substitution path)
    | Hole -> Hole

let close env = close' env 0
let close_locator env = close_locator' env 0
let close_abs env = close_abs' env 0

(* --- *)

let reabstract env (T.Exists (params, locator, body)) =
    let params' = Vector.map (fun kind -> Env.generate env (Name.fresh (), kind)) params in
    let substitution = Vector.map (fun ov -> T.Ov ov) params' in
    ( params'
    , expose_locator env substitution locator
    , expose env substitution body )

let instantiate_abs env (T.Exists (existentials, locator, body)) =
    let uvs = Vector.map (fun _ -> Env.uv env (Name.fresh ())) existentials in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , expose_locator env substitution locator
    , expose env substitution body )

let instantiate_arrow env universals domain eff codomain =
    let uvs = Vector.map (fun _ -> Env.uv env (Name.fresh())) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , Vector.map (fun (locator, param) ->
        ( expose_locator env substitution locator
        , expose env substitution param ))
        domain
    , eff
    , expose_abs env substitution codomain )

