open Streaming
open Asserts

module T = Fc.Type
module Uv = Fc.Uv
module E = Fc.Term.Expr
module TS = TyperSigs

type var = Util.plicity * E.var

(*
type vals_binding =
    | White of (T.ov Vector.t * T.t) * Ast.Term.Expr.t with_pos
    | Grey
    | Black of Fc.Term.Expr.t TS.typing

type row_binding =
    | WhiteT of (T.ov Vector.t * T.t) * Ast.Type.t with_pos
    | GreyT
    | BlackT of T.t TS.kinding
*)

type scope =
    (*| Hoisting of T.ov list TxRef.t * T.level
    | Rigid of T.ov Vector.t*)
    | Vals of var Name.Map.t
(*    | Rec of (var * vals_binding TxRef.rref) Name.Map.t * E.var list TxRef.rref
    | Row of (var * row_binding TxRef.rref) Name.Map.t * E.var list TxRef.rref
    | Axiom of (Name.t * T.ov * uv) Name.Map.t*)

type env =
    { errorHandler : Util.span -> TypeError.t -> unit
    (*; tx_log : Fc.Uv.subst*)
    ; scopes : scope list
    ; t_binders : T.binder list }

module Make
    (C : TS.TYPING with type env = env)
    (K : TS.KINDING with type env = env)
    (M : TS.MATCHING with type env = env)
: TS.ENV with type t = env
= struct

module T = T

module Bindings = Map.Make(Name)

let (!) = TxRef.(!)
let (:=) = TxRef.(:=)

type t = env

type error_handler = Util.span -> TypeError.t -> unit

let raiseError pos error = raise (TypeError.TypeError (pos, error))

let global_binder =
    Uv.Scope (Global {bindees = TxRef.ref Vector.empty; ovs = TxRef.ref Vector.empty})

let program () =
    { errorHandler = raiseError
    (*; tx_log = Fc.Uv.new_subst ()*)
    ; scopes = [(*Hoisting (ref [], initial_level)*)]
    ; t_binders = [global_binder] }

let interactive () =
    { errorHandler = raiseError
    (*; tx_log = Fc.Uv.new_subst ()*)
    ; scopes = [(*Hoisting (ref [], initial_level)*)]
    ; t_binders = [global_binder] }

let eval () =
    { errorHandler = raiseError
    (*; tx_log = Fc.Uv.new_subst ()*)
    ; scopes = [(*Hoisting (ref [], initial_level)*)]
    ; t_binders = [global_binder] }

let reportError (env : t) pos error = env.errorHandler pos error

let with_error_handler (env : t) errorHandler = {env with errorHandler}

let push_val plicity (env : t) (var : E.var) =
    match env.scopes with
    | Vals bindings :: scopes' ->
        {env with scopes = Vals (Name.Map.add var.name (plicity, var) bindings) :: scopes'}
    | scopes ->
        {env with scopes = Vals (Name.Map.singleton var.name (plicity, var)) :: scopes}

let push_level env =
    match env.t_binders with
    | [Uv.Scope parent] ->
        let scope = Uv.Local {level = Uv.Scope.level parent + 1; parent
            ; bindees = TxRef.ref Vector.empty; ovs = TxRef.ref Vector.empty} in
        ({env with t_binders = [Scope scope]}, scope)
    | _ -> unreachable None

let in_bound (env : t) uv f =
    let level = match env.t_binders with
        | binder :: _ -> Uv.Binder.level binder + 1
        | _ -> unreachable None in
    let binder = Uv.Type uv in
    uv.level := level;
    let env = {env with t_binders = binder :: env.t_binders} in
    Fun.protect (fun () -> f env)
        ~finally: (fun () -> uv.level := -1)

let in_bounds (env : t) uv (uv' : Uv.t) f =
    let level = match env.t_binders with
        | binder :: _ -> Uv.Binder.level binder + 1
        | _ -> unreachable None in
    let binder = Uv.Type uv in
    uv.level := level;
    uv'.level := level;
    let env = {env with t_binders = binder :: env.t_binders} in
    Fun.protect (fun () -> f env)
        ~finally: (fun () ->
            uv.level := -1;
            uv.level := -1)

(*
let push_rec env stmts =
    let bindings = CCVector.fold (fun bindings (defs, semiabs, expr) ->
        Vector.fold (fun bindings (var : E.var) ->
            Name.Map.add var.name ((Util.Explicit, var)
                , ref (White (semiabs, expr))) bindings
        ) bindings defs
    ) Name.Map.empty stmts in
    let fields = ref [] in
    ({env with scopes = Rec (bindings, fields) :: env.scopes}, fields)

let push_row env decls =
    let bindings = CCVector.fold (fun bindings (defs, semiabs, rhs) ->
        Vector.fold (fun bindings (var : E.var) ->
            Name.Map.add var.name ((Util.Explicit, var)
                , ref (WhiteT (semiabs, rhs))) bindings
        ) bindings defs
    ) Name.Map.empty decls in
    let fields = ref [] in
    ({env with scopes = Row (bindings, fields) :: env.scopes}, fields)

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
    if Vector.length axioms > 0 then begin
        let bindings = Vector.fold (fun bindings ((_, ((k, _), _), _) as v) ->
            Name.Map.add k v bindings
        ) Name.Map.empty axioms in
        {env with scopes = Axiom bindings :: env.scopes}
    end else env

let generate env binding =
    let rec generate = function
        | Hoisting (bindings, level) :: _ ->
            let ov = (binding, level) in
            TxRef.set env.tx_log bindings (ov :: !bindings);
            ov
        | _ :: scopes' -> generate scopes'
        | [] -> unreachable None in
    generate env.scopes

let get_implementation (env : t) (((name, _), _) : T.ov) =
    let rec get = function
        | Axiom kvs :: scopes ->
            (match Name.Map.find_opt name kvs with
            | Some axiom -> Some axiom
            | None -> get scopes)
        | _ :: scopes -> get scopes
        | [] -> None
    in get env.scopes

let type_fns (env : t) =
    let rec loop = function
        | [Hoisting (ovs, _)] ->
            let tfns = CCVector.create () in
            List.iter (fun (binding, _) -> CCVector.push tfns binding) !ovs;
            Vector.build tfns
        | _ :: scopes' -> loop scopes'
        | [] -> unreachable None in
    loop env.scopes

let uv (env : t) kind = Fc.Uv.make env.tx_log kind env.level

let get_uv (env : t) uv = Fc.Uv.get env.tx_log uv

(* OPTIMIZE: *)
let set_uv (env : t) pos uv v = match get_uv env uv with
    | Unassigned (_, kind, _) ->
        (match v with
        | Uv.Unassigned _ -> ()
        | Assigned typ -> ignore (M.solving_unify pos env kind (K.kindof_F pos env typ)));
        Fc.Uv.set env.tx_log uv v
    | Assigned _ -> bug (Some pos) ~msg: "tried to set Assigned uv"

let sibling (env : t) kind uv = match get_uv env uv with
    | Unassigned (_, _, level) -> Fc.Uv.make env.tx_log kind level
    | Assigned _ -> unreachable None

let set_expr (env : t) ref expr = TxRef.set env.tx_log ref expr
let set_coercion (env : t) ref coercion = TxRef.set env.tx_log ref coercion

let transaction (env : t) thunk = TxRef.transaction env.tx_log thunk*)

(*
let reabstract env : T.t -> T.ov Vector.t * T.t = function
    | Exists (params, body) ->
        let params = Vector1.to_vector params in
        let params = Vector.map (fun kind -> generate env (Name.fresh (), kind)) params in
        let substitution = Vector.map (fun ov -> T.Ov ov) params in
        (params, expose env substitution body)
    | typ -> (Vector.empty, typ)*)

(*
let push_abs_skolems env existentials body =
    let (env, skolems) = push_skolems env (Vector1.to_vector existentials) in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    (env, Option.get (Vector1.of_vector skolems), expose env substitution body)

let push_arrow_skolems env universals domain eff codomain =
    let (env, skolems) = push_skolems env universals in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    ( env, skolems
    , expose env substitution domain
    , expose env substitution eff
    , expose env substitution codomain )

let push_impli_skolems env universals domain codomain =
    let (env, skolems) = push_skolems env universals in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    ( env, skolems
    , expose env substitution domain
    , expose env substitution codomain )

let instantiate_abs env existentials body =
    let uvs = Vector1.map (uv env) existentials in
    let substitution = uvs |> Vector1.to_vector |> Vector.map (fun uv -> T.Uv uv) in
    (uvs, expose env substitution body)

let instantiate_arrow env universals domain eff codomain =
    let uvs = Vector.map (uv env) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , expose env substitution domain
    , expose env substitution eff
    , expose env substitution codomain )

let instantiate_impli env universals domain codomain =
    let uvs = Vector.map (uv env) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , expose env substitution domain
    , expose env substitution codomain )

let instantiate_primop env universals domain app_eff codomain =
    let uvs = Vector.map (uv env) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , Vector.map (expose env substitution) domain
    , expose env substitution app_eff
    , expose env substitution codomain )

let instantiate_branch env universals domain app_eff codomain =
    let uvs = Vector.map (uv env) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , Vector.map (expose env substitution) domain
    , expose env substitution app_eff
    , Vector.map (expose env substitution) codomain )*)

let t_scope (env : t) = match env.t_binders with
    | [Scope scope] -> scope
    | _ -> unreachable None

let find (env : t) pos name =
    let rec find scopes = match scopes with
        | Vals bindings :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some (_, var) -> (match scopes' with
                | [(*Hoisting _*)] -> (var, true)
                | _ -> (var, false))
            | None -> find scopes')
        (*| Rec (bindings, fields) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some ((_, var), binding) ->
                (match !binding with
                | White (semiabs, expr) ->
                    let env = {env with scopes} in
                    TxRef.set env.tx_log binding Grey;
                    let typing = C.implement env semiabs expr in
                    TxRef.set env.tx_log binding (Black typing);
                    TxRef.set env.tx_log fields (var :: !fields)
                | Grey -> () (* TODO: really? *)
                | Black _ -> ());
                (var, false)
            | None -> find scopes')
        | Row (bindings, fields) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some ((_, var), binding) ->
                (match !binding with
                | WhiteT ((_, lhs), rhs) ->
                    let env = {env with scopes} in
                    TxRef.set env.tx_log binding GreyT;
                    let {TS.typ = rhs; kind = _} as kinding = K.kindof env rhs in
                    let (_, rhs) = reabstract env rhs in
                    ignore (M.solving_subtype pos env rhs lhs);
                    TxRef.set env.tx_log binding (BlackT kinding);
                    TxRef.set env.tx_log fields (var :: !fields)
                | GreyT -> () (* TODO: really? *)
                | BlackT _ -> ());
                (var, false)
            | None -> find scopes')
        | (Hoisting _ | Rigid _ | Axiom _) :: scopes -> find scopes*)
        | [] ->
            reportError env pos (Unbound name);
            todo (Some pos)
            (*(E.fresh_var (T.Uv (uv env (Uv (uv env T.aKind)))), false)*) in
    find env.scopes

let find_rhs (env : t) pos name =
    let rec find scopes = match scopes with
        | Vals bindings :: scopes -> (match Name.Map.find_opt name bindings with
            | Some _ -> bug (Some pos) ~msg: "`Env.find_rhs` found `Vals` scope"
            | None -> find scopes)
        (*| Rec (bindings, fields) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some ((_, var), binding) ->
                (match !binding with
                | White (semiabs, expr) ->
                    let env = {env with scopes} in
                    TxRef.set env.tx_log binding Grey;
                    let typing = C.implement env semiabs expr in
                    TxRef.set env.tx_log binding (Black typing);
                    TxRef.set env.tx_log fields (var :: !fields);
                    typing
                | Grey -> bug (Some pos) ~msg: "`Env.find_rlhs` found `Grey` binding"
                | Black typing -> typing)
            | None -> find scopes')
        | Row (bindings, _) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some _ -> bug (Some pos) ~msg: "`Env.find_rhs` found `Row` scope."
            | None -> find scopes')
        | (Hoisting _ | Rigid _ | Axiom _) :: scopes -> find scopes*)
        | [] ->
            reportError env pos (Unbound name);
            todo (Some pos)
            (*let typ = T.Uv (uv env (Uv (uv env T.aKind))) in
            {term = E.at pos typ (E.use (E.fresh_var typ)); eff = EmptyRow}*) in
    find env.scopes

let find_rhst (env : t) pos name =
    let rec find scopes = match scopes with
        | Vals bindings :: scopes -> (match Name.Map.find_opt name bindings with
            | Some _ -> bug (Some pos) ~msg: "`Env.find_rhs` found `Vals` scope"
            | None -> find scopes)
        (*| Rec (bindings, _) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some _ -> bug (Some pos) ~msg: "`Env.find_rhst` found `Rec` scope."
            | None -> find scopes')
        | Row (bindings, fields) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some ((_, var), binding) ->
                (match !binding with
                | WhiteT ((_, lhs), rhs) ->
                    let env = {env with scopes} in
                    TxRef.set env.tx_log binding GreyT;
                    let {TS.typ = rhs; kind = _} as kinding = K.kindof env rhs in
                    let (_, rhs) = reabstract env rhs in
                    ignore (M.solving_subtype pos env rhs lhs);
                    TxRef.set env.tx_log binding (BlackT kinding);
                    TxRef.set env.tx_log fields (var :: !fields);
                    kinding
                | GreyT -> bug (Some pos) ~msg: "`Env.find_rhst` found `GreyT` binding"
                | BlackT kinding -> kinding)
            | None -> find scopes')
        | (Hoisting _ | Rigid _ | Axiom _) :: scopes -> find scopes*)
        | [] ->
            reportError env pos (Unbound name);
            todo (Some pos)
            (*let kind = T.Uv (uv env T.aKind) in
            {typ = T.Uv (uv env kind); kind}*) in
    find env.scopes

let scope_vars = function
    | Vals bindings ->
        Stream.from (Source.seq (Name.Map.to_seq bindings))
        |> Stream.map snd
    (*| Rec (bindings, _) ->
        Stream.from (Source.seq (Name.Map.to_seq bindings))
        |> Stream.map (fun (_, (var, _)) -> var)
    | Row (bindings, _) ->
        Stream.from (Source.seq (Name.Map.to_seq bindings))
        |> Stream.map (fun (_, (var, _)) -> var)
    | Hoisting _ | Rigid _ | Axiom _ -> Stream.empty*)

let implicits (env : t) = Stream.from (Source.list env.scopes)
    |> Stream.flat_map scope_vars
    |> Stream.filter (function (Util.Explicit, _) -> false | (Implicit, _) -> true)
    |> Stream.map snd

let tv env kind = T.Uv (Uv.fresh ForAll (Scope (t_scope env)) kind)

let forall_scope_ovs env scope t = T.forall_scope_ovs ~binder: (t_scope env) scope t
let instantiate env t = T.instantiate (t_scope env) t

let reabstract span env scope t =
    let t = T.force t in
    match t with
    | Uv root ->
        t |> T.postwalk_rebinding (fun t -> match t with
            | Uv {name = _; quant = Exists; binder; bindees = _; level = _; bound = _} ->
                (match !binder with
                | Uv.Type binder when Uv.equal binder root ->
                    Ov (Uv.Scope.fresh_ov scope (K.kindof_F span env t))
                | _ -> t)
            | t -> t)
    | t -> t

end

