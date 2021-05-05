open Asserts

module T = Fc.Type
module FExpr = Fc.Term.Expr
type var = FExpr.var
type expr = Fc.Term.Expr.t
module Tx = Transactional
open Tx.Ref

type error_handler = TypeError.t -> unit

type scope =
    | Hoisting of T.ov list Tx.Ref.t * T.level
    | Rigid of T.ov Vector.t
    | Vals of var Name.Map.t

type t =
    { namespace : Namespace.t option
    ; scopes : scope list
    ; level : T.level
    ; error_handler : error_handler }

let report_error (env : t) err = env.error_handler err

let with_error_handler (env : t) error_handler = {env with error_handler}

let empty =
    { namespace = None
    ; scopes = []
    ; level = 1
    ; error_handler = fun err -> unreachable (Some err.pos) }

let toplevel namespace =
    { namespace = Some namespace
    ; scopes = []
    ; level = 1
    ; error_handler = fun err -> unreachable (Some err.pos) }

let namespace (env : t) = env.namespace

let type_fns _ = Vector.empty (* TODO *)

let uv env is_fwd kind = ref (T.Unassigned (is_fwd, Name.fresh (), kind, env.level))

let some_type_kind env is_fwd =
    T.App {callee = Prim TypeIn; arg = Uv (uv env is_fwd (Prim Rep))}

let push_val is_global (env : t) (var : var) =
    if is_global
    then match env.namespace with
        | Some ns -> {env with namespace = Some (Namespace.add ns var)}
        | None -> unreachable None
    else match env.scopes with
        | Vals bindings :: scopes' ->
            {env with scopes = Vals (Name.Map.add var.name var bindings) :: scopes'}
        | scopes ->
            {env with scopes = Vals (Name.Map.singleton var.name var) :: scopes}

let find_val (env : t) span name =
    let rec find = function
        | Vals kvs :: scopes -> (match Name.Map.find_opt name kvs with
            | Some var -> FExpr.at span var.vtyp (FExpr.use var)
            | None -> find scopes)
        | (Rigid _ | Hoisting _) :: scopes -> find scopes
        | [] ->
            (match Option.bind env.namespace (Fun.flip Namespace.find_typ name) with
            | Some {vtyp = typ; plicity = _; name = _} ->
                let namexpr = FExpr.at span (Prim String)
                    (FExpr.const (String (Name.to_string name))) in
                FExpr.primapp GlobalGet (Vector.singleton typ) (Vector.singleton namexpr)
                |> FExpr.at span typ
            | None ->
                report_error env ({v = Unbound name; pos = span});
                (* FIXME: levels: *)
                let typ = T.Uv (uv env false (some_type_kind env false)) in
                FExpr.at span typ (FExpr.use (FExpr.var Explicit name typ))) in
    find env.scopes

let push_existential (env : t) =
    let bindings = ref [] in
    let level = env.level + 1 in
    ( {env with scopes = Hoisting (bindings, level) :: env.scopes; level}
    , bindings )

let generate env (name, kind) =
    let rec generate = function
        | Hoisting (bindings, level) :: _ ->
            let ov = {T.name; kind; level} in
            bindings := (ov :: !bindings);
            ov
        | _ :: scopes' -> generate scopes'
        | [] -> unreachable None in
    generate env.scopes

let reabstract env : T.t -> T.ov Vector.t * T.t = function
    | Exists {existentials; body} ->
        let existentials = Vector1.to_vector existentials in
        let existentials = Vector.map (fun kind -> generate env (Name.fresh (), kind)) existentials in
        let substitution = Vector.map (fun ov -> T.Ov ov) existentials in
        (existentials, T.expose substitution body)
    | typ -> (Vector.empty, typ)

let push_skolems (env : t) kinds =
    let level = env.level + 1 in
    let skolems = Vector.map (fun kind -> {T.name = Name.fresh (); kind; level}) kinds in
    ( {env with scopes = Rigid skolems :: env.scopes; level}
    , skolems )

let push_arrow_skolems env universals domain eff codomain =
    let (env, skolems) = push_skolems env universals in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    ( env, skolems
    , T.expose substitution domain
    , T.expose substitution eff
    , T.expose substitution codomain )

let instantiate_arrow env universals domain eff codomain =
    let uvs = Vector.map (uv env false) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , T.expose substitution domain
    , T.expose substitution eff
    , T.expose substitution codomain )

