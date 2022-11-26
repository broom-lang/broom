open Streaming
open Asserts

module T = Fc.Type
module FExpr = Fc.Term.Expr
type var = FExpr.var
type span = Util.span
module Tx = Transactional
open Tx.Ref

type error_handler = TypeError.t -> unit

type val_binding =
    | White of {span : span; pat : Ast.Expr.t; expr : Ast.Expr.t}
    | Grey of {span : span; pat : Ast.Expr.t; expr : Ast.Expr.t}
    | Black of {span : span; pat : FExpr.pat; expr : FExpr.t option}

type row_binding =
    | WhiteT of {span : span; pat : Ast.Expr.t; typ : Ast.Expr.t}
    | GreyT of span
    | BlackT of {span : span; typ : T.t}

type nonrec_scope = var Name.HashMap.t * val_binding Tx.Ref.t

type rec_scope = (var * val_binding Tx.Ref.t) Name.HashMap.t

type row_scope = (var * row_binding Tx.Ref.t) Name.HashMap.t

type scope =
    | Hoisting of T.ov list Tx.Ref.t * T.level
    | Rigid of T.ov Vector.t
    | NonRec of nonrec_scope
    | Rec of rec_scope
    | Row of row_scope

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

let scopes (env : t) = env.scopes

let push_nonrec (env : t) scope = {env with scopes = NonRec scope :: env.scopes}

let push_rec (env : t) bindings = {env with scopes = Rec bindings :: env.scopes}

let push_row (env : t) scope = {env with scopes = Row scope :: env.scopes}

let push_param env (var : var) (pat : FExpr.pat) =
    let scope = Name.HashMap.singleton var.name var in
    let binding = ref (Black {span = pat.ppos; pat; expr = None}) in
    push_nonrec env (scope, binding)

let find_val (env : t) name =
    (*let rec find = function
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
    find env.scopes*)

    let rec find scopes =
        match scopes with
        | NonRec (vars, binding) :: scopes' ->
            (match Name.HashMap.get name vars with
            | Some var -> Some (var, binding, {env with scopes = scopes})
            | None -> find scopes')

        | Rec bindings :: scopes' ->
            (match Name.HashMap.get name bindings with
            | Some (var, binding) -> Some (var, binding, {env with scopes = scopes})
            | None -> find scopes')

        | (Rigid _ | Hoisting _) :: scopes' -> find scopes'
        | [] -> None
        | _ -> todo None in

    find env.scopes

let scope_vars = function
    | NonRec (vars, _) ->
        Stream.from (Name.HashMap.to_source vars)
        |> Stream.map snd
    | Rec bindings ->
        Stream.from (Name.HashMap.to_source bindings)
        |> Stream.map (fun (_, (var, _)) -> var)
    | Row bindings ->
        Stream.from (Name.HashMap.to_source bindings)
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

type env = t

module NonRecScope = struct
    type t = nonrec_scope

    (* FIXME: prevent duplicates: *)
    module Builder = struct
        type scope = t
        type t =
            { transient : CCHashTrie.Transient.t
            ; mutable vars : var Name.HashMap.t }

        let create () =
            { transient = CCHashTrie.Transient.create ()
            ; vars = Name.HashMap.empty }

        let var env ({transient; vars} as builder) plicity name =
            let typ = T.Uv (uv env false (some_type_kind env false)) in
            let var = FExpr.fresh_var plicity typ in
            builder.vars <- Name.HashMap.add_mut ~id: transient name var vars;
            var

        let build {vars; transient} span pat expr =
            CCHashTrie.Transient.freeze transient;
            (vars, ref (Black {span; pat; expr}))
    end
end

module RecScope = struct
    type t = rec_scope

    (* FIXME: prevent duplicates: *)
    module Builder = struct
        type scope = t
        type t =
            { transient : CCHashTrie.Transient.t
            ; mutable scope : scope }

        let create () =
            { transient = CCHashTrie.Transient.create ()
            ; scope = Name.HashMap.empty }

        let binding _ span pat expr = ref (White {span; pat; expr})

        let var env ({transient; scope} as builder) binding plicity name =
            let typ = T.Uv (uv env true (some_type_kind env false)) in
            let var = FExpr.fresh_var plicity typ in
            builder.scope <- Name.HashMap.add_mut ~id: transient name (var, binding) scope;
            var

        let build {scope; transient} =
            CCHashTrie.Transient.freeze transient;

            scope |> Name.HashMap.iter ~f: (fun _ ((var : var), _) ->
                match var.vtyp with
                | Uv uv ->
                    (match !uv with
                    | Unassigned (_, name, kind, level) ->
                        uv := Unassigned (false, name, kind, level)
                    | Assigned _ -> ())
                | _ -> unreachable None
            );

            scope
    end
end

module RowScope = struct
    type t = row_scope

    (* FIXME: prevent duplicates: *)
    module Builder = struct
        type scope = t
        type t =
            { transient : CCHashTrie.Transient.t
            ; mutable scope : scope }

        let create () =
            { transient = CCHashTrie.Transient.create ()
            ; scope = Name.HashMap.empty }

        let binding _ span pat typ = ref (WhiteT {span; pat; typ})

        let var env ({transient; scope} as builder) binding plicity name =
            let typ = T.Uv (uv env true (some_type_kind env false)) in
            let var = FExpr.fresh_var plicity typ in
            builder.scope <- Name.HashMap.add_mut ~id: transient name (var, binding) scope;
            var

        let build {scope; transient} =
            CCHashTrie.Transient.freeze transient;

            scope |> Name.HashMap.iter ~f: (fun _ ((var : var), _) ->
                match var.vtyp with
                | Uv uv ->
                    (match !uv with
                    | Unassigned (_, name, kind, level) ->
                        uv := Unassigned (false, name, kind, level)
                    | Assigned _ -> ())
                | _ -> unreachable None
            );

            scope
    end
end

