open Streaming
open Asserts

module T = Fc.Type
module FExpr = Fc.Term.Expr
type var = FExpr.var
type span = Util.span
type 'a with_pos = 'a Util.with_pos
module Tx = Transactional
open Tx.Ref

type 'a kinding = {typ : 'a; kind : T.kind} (* HACK *)

type error_handler = TypeError.t -> unit

type row_binding =
    | WhiteT of T.t * Ast.Type.t with_pos
    | GreyT
    | BlackT of T.t kinding

type scope =
    | Hoisting of T.ov list Tx.Ref.t * T.level
    | Rigid of T.ov Vector.t
    | Vals of var Name.Map.t
    | Row of (var * row_binding Tx.Ref.t) Name.Map.t

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

let push_row env decls =
    let bindings = CCVector.fold (fun bindings (vars, lhs, rhs) ->
        Vector.fold (fun bindings (var : FExpr.var) ->
            Name.Map.add var.name (var, ref (WhiteT (lhs, rhs))) bindings
        ) bindings vars
    ) Name.Map.empty decls in
    {env with scopes = Row bindings :: env.scopes}

let find_val elaborate subtype (env : t) span name =
    let rec find = function
        | Vals kvs :: scopes -> (match Name.Map.find_opt name kvs with
            | Some var -> FExpr.at span var.vtyp (FExpr.use var)
            | None -> find scopes)

        | (Row bindings :: scopes') as scopes ->
            (match Name.Map.find_opt name bindings with
            | Some (var, binding) ->
                (match !binding with
                | WhiteT (lhs, rhs) ->
                    let env = {env with scopes} in
                    binding := GreyT;
                    let (rhs, kind) = elaborate env rhs in
                    let (_, rhs) = reabstract env rhs in
                    subtype span env rhs lhs;
                    binding := BlackT {typ = rhs; kind}
                | GreyT -> () (* TODO: really? *)
                | BlackT _ -> ());
                FExpr.at span var.vtyp (FExpr.use var)
            | None -> find scopes')

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

let force_typ elaborate subtype (env : t) span name =
    let rec find scopes = match scopes with
        | Vals bindings :: scopes -> (match Name.Map.find_opt name bindings with
            | Some _ -> bug (Some span) ~msg: "`Env.find_rhs` found `Vals` scope"
            | None -> find scopes)

        | Row bindings :: scopes' ->
            (match Name.Map.find_opt name bindings with
            | Some (_, binding) ->
                (match !binding with
                | WhiteT (lhs, rhs) ->
                    let env = {env with scopes} in
                    binding := GreyT;
                    let (rhs, kind) = elaborate env rhs in
                    let (_, rhs) = reabstract env rhs in
                    subtype span env rhs lhs;
                    binding := BlackT {typ = rhs; kind};
                    ()
                | GreyT -> bug (Some span) ~msg: "`Env.find_rhst` found `GreyT` binding"
                | BlackT _ -> ())
            | None -> find scopes')

        | (Hoisting _ | Rigid _) :: scopes -> find scopes

        | [] -> report_error env ({v = Unbound name; pos = span}) in
    find env.scopes

let scope_vars = function
    | Vals bindings ->
        Stream.from (Source.seq (Name.Map.to_seq bindings))
        |> Stream.map snd
    | Row bindings ->
        Stream.from (Source.seq (Name.Map.to_seq bindings))
        |> Stream.map (fun (_, (var, _)) -> var)
    | Hoisting _ | Rigid _ -> Stream.empty

let implicits (env : t) =
    Stream.from (Source.list env.scopes)
    |> Stream.flat_map scope_vars
    |> Stream.filter (fun {FExpr.plicity; _} -> Util.is_implicit plicity)

let push_skolems (env : t) kinds =
    let level = env.level + 1 in
    let skolems = Vector.map (fun kind -> {T.name = Name.fresh (); kind; level}) kinds in
    ( {env with scopes = Rigid skolems :: env.scopes; level}
    , skolems )

let push_abs_skolems env existentials body =
    let (env, skolems) = push_skolems env (Vector1.to_vector existentials) in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    (env, Option.get (Vector1.of_vector skolems), T.expose substitution body)

let instantiate_abs env existentials body =
    let uvs = Vector1.map (uv env false) existentials in
    let substitution = uvs |> Vector1.to_vector |> Vector.map (fun uv -> T.Uv uv) in
    (uvs, T.expose substitution body)

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

let push_impli_skolems env universals domain codomain =
    let (env, skolems) = push_skolems env universals in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    ( env, skolems
    , T.expose substitution domain
    , T.expose substitution codomain )

let instantiate_impli env universals domain codomain =
    let uvs = Vector.map (uv env false) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , T.expose substitution domain
    , T.expose substitution codomain )

let instantiate_primop env universals domain app_eff codomain =
    let uvs = Vector.map (uv env false) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , Vector.map (T.expose substitution) domain
    , T.expose substitution app_eff
    , T.expose substitution codomain )

let instantiate_branch env universals domain app_eff codomain =
    let uvs = Vector.map (uv env false) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , Vector.map (T.expose substitution) domain
    , T.expose substitution app_eff
    , Vector.map (T.expose substitution) codomain )

