module T = Fc.Type
module E = Fc.Term.Expr
module TS = TyperSigs

type 'a with_pos = 'a Util.with_pos
type uv = Fc.Uv.t
type var = E.var

type vals_binding =
    | White of (T.ov Vector.t * T.t) * Ast.Term.Expr.t with_pos
    | Grey
    | Black of Fc.Term.Expr.t TS.typing

type row_binding =
    | WhiteT of (T.ov Vector.t * T.t) * Ast.Type.t with_pos
    | GreyT
    | BlackT of T.t TS.kinding

type scope =
    | Hoisting of T.ov list TxRef.rref * T.level
    | Rigid of T.ov Vector.t
    | Val of Fc.Term.Expr.var
    | Vals of (var * vals_binding TxRef.rref) Name.Map.t * var list TxRef.rref
    | Row of (var * row_binding TxRef.rref) Name.Map.t * var list TxRef.rref
    | Axiom of (Name.t * T.ov * uv) Name.Map.t

type env =
    { errorHandler : Util.span -> TypeError.t -> unit
    ; tx_log : Fc.Uv.subst
    ; scopes : scope list
    ; level : Fc.Type.level }

module Make
    (C : TS.TYPING with type env = env)
    (K : TS.KINDING with type env = env)
    (M : TS.MATCHING with type env = env)
: TS.ENV with type t = env
= struct

module T = T
module Uv = Fc.Uv

module Bindings = Map.Make(Name)

let ref = TxRef.ref
let (!) = TxRef.(!)

type uv = Fc.Uv.t

type t = env

let raiseError pos error = raise (TypeError.TypeError (pos, error))

let initial_level = 1

let program () =
    { errorHandler = raiseError
    ; tx_log = Fc.Uv.new_subst ()
    ; scopes = [Hoisting (ref [], initial_level)]
    ; level = initial_level }

let interactive () =
    { errorHandler = raiseError
    ; tx_log = Fc.Uv.new_subst ()
    ; scopes = [Hoisting (ref [], initial_level)]
    ; level = initial_level }

let eval () =
    { errorHandler = raiseError
    ; tx_log = Fc.Uv.new_subst ()
    ; scopes = [Hoisting (ref [], initial_level)]
    ; level = initial_level }

let reportError (env : t) pos error = env.errorHandler pos error

let wrapErrorHandler (env : t) middleware =
    {env with errorHandler = middleware env.errorHandler}

let push_val (env : t) var = {env with scopes = Val var :: env.scopes}

let push_rec env stmts =
    let bindings = CCVector.fold (fun bindings (defs, semiabs, expr) ->
        Vector.fold (fun bindings (var : var) ->
            Name.Map.add var.name (var, ref (White (semiabs, expr))) bindings
        ) bindings defs
    ) Name.Map.empty stmts in
    let fields = ref [] in
    ({env with scopes = Vals (bindings, fields) :: env.scopes}, fields)

let push_row env decls =
    let bindings = CCVector.fold (fun bindings (defs, semiabs, rhs) ->
        Vector.fold (fun bindings (var : var) ->
            Name.Map.add var.name (var, ref (WhiteT (semiabs, rhs))) bindings
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

let type_fns (env : t) = match env.scopes with
    | [Hoisting (ovs, _)] ->
        let tfns = CCVector.create () in
        List.iter (fun (binding, _) -> CCVector.push tfns binding) !ovs;
        Vector.build tfns
    | _ -> failwith "compiler bug: type_fns on non-toplevel environment"

let uv (env : t) kind = Fc.Uv.make env.tx_log kind env.level

let get_uv (env : t) uv = Fc.Uv.get env.tx_log uv

(* OPTIMIZE: *)
let set_uv (env : t) pos uv v = match get_uv env uv with
    | Unassigned (_, kind, _) ->
        (match v with
        | Uv.Unassigned _ -> ()
        | Assigned typ -> ignore (M.solving_unify pos env kind (K.kindof_F pos env typ)));
        Fc.Uv.set env.tx_log uv v
    | Assigned _ -> failwith "compiler bug: tried to set Assigned uv"

let sibling (env : t) kind uv = match get_uv env uv with
    | Unassigned (_, _, level) -> Fc.Uv.make env.tx_log kind level
    | Assigned _ -> failwith "unreachable"

let set_expr (env : t) ref expr = TxRef.set env.tx_log ref expr
let set_coercion (env : t) ref coercion = TxRef.set env.tx_log ref coercion

let document (env : t) to_doc v = to_doc env.tx_log v

let rec expose' env depth substitution : T.t -> T.t = function
    | Exists (params, body) ->
        let depth = depth + 1 in
        Exists (params, expose' env depth substitution body)
    | PromotedArray typs -> PromotedArray (Vector.map (expose' env depth substitution) typs)
    | PromotedTuple typs -> PromotedTuple (Vector.map (expose' env depth substitution) typs)
    | Tuple typs -> Tuple (Vector.map (expose' env depth substitution) typs)
    | Pi {universals; domain; codomain} ->
        let depth = depth + 1 in
        Pi { universals
            ; domain = Ior.bimap (expose' env depth substitution)
                (fun {T.edomain; eff} ->
                    { T.edomain = expose' env depth substitution edomain
                    ; eff = expose' env depth substitution eff })
                domain
            ; codomain = expose' env depth substitution codomain }
    | Record row -> Record (expose' env depth substitution row)
    | With {base; label; field} ->
        With {base = expose' env depth substitution base; label; field = expose' env depth substitution field}
    | EmptyRow -> EmptyRow
    | Proxy typ -> Proxy (expose' env depth substitution typ)
    | Fn (params, body) -> Fn (params, expose' env (depth + 1) substitution body)
    | App (callee, arg) -> App (expose' env depth substitution arg, expose' env depth substitution callee)
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
    | T.TupleL _ as template -> template
    | PiL codomain -> T.PiL (expose_template' env depth substitution codomain)
    | WithL {base; label; field} ->
        WithL { base = expose_template' env depth substitution base
              ; label; field = expose_template' env depth substitution field }
    | ProxyL path -> ProxyL (expose' env depth substitution path)
    | Hole -> Hole

let expose env = expose' env 0
let expose_template env = expose_template' env 0

(* --- *)

let rec close' env depth substitution : T.t -> T.t = function
    | Exists (params, body) ->
        let depth = depth + 1 in
        Exists (params, close' env depth substitution body)
    | PromotedArray typs -> PromotedArray (Vector.map (close' env depth substitution) typs)
    | PromotedTuple typs -> PromotedTuple (Vector.map (close' env depth substitution) typs)
    | Tuple typs -> Tuple (Vector.map (close' env depth substitution) typs)
    | Pi {universals; domain; codomain} ->
        let depth = depth + 1 in
        Pi { universals
           ; domain = Ior.bimap (close' env depth substitution)
                (fun {T.edomain; eff} ->
                    { T.edomain = close' env depth substitution edomain
                    ; eff = close' env depth substitution eff })
                domain
           ; codomain = close' env depth substitution codomain }
    | Record row -> Record (close' env depth substitution row)
    | With {base; label; field} ->
        With {base = close' env depth substitution base; label; field = close' env depth substitution field}
    | EmptyRow -> EmptyRow
    | Proxy typ -> Proxy (close' env depth substitution typ)
    | Fn (params, body) -> Fn (params, close' env (depth + 1) substitution body)
    | App (callee, arg) -> App (close' env depth substitution callee, close' env depth substitution arg)
    | Ov ((name, kind), _) as path ->
        Name.Map.find_opt name substitution
            |> Option.fold ~some: (fun sibli -> Bv {depth; sibli; kind}) ~none: path
    | Uv uv as typ ->
        (match get_uv env uv with
        | Assigned typ -> close' env depth substitution typ
        | Unassigned _ -> typ)
    | (Bv _ | Prim _) as typ -> typ

and close_template' env depth substitution = function
    | T.TupleL _ as template -> template
    | T.PiL codomain -> T.PiL (close_template' env depth substitution codomain)
    | WithL {base; label; field} ->
        WithL { base = close_template' env depth substitution base
              ; label; field = close_template' env depth substitution field }
    | ProxyL path -> ProxyL (close' env depth substitution path)
    | Hole -> Hole

let close env = close' env 0
let close_template env = close_template' env 0

(* --- *)

let reabstract env : T.t -> T.ov Vector.t * T.t = function
    | Exists (params, body) ->
        let params = Vector1.to_vector params in
        let params = Vector.map (fun kind -> generate env (Name.fresh (), kind)) params in
        let substitution = Vector.map (fun ov -> T.Ov ov) params in
        (params, expose env substitution body)
    | typ -> (Vector.empty, typ)

let push_abs_skolems env existentials body =
    let (env, skolems) = push_skolems env (Vector1.to_vector existentials) in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    (env, Option.get (Vector1.of_vector skolems), expose env substitution body)

let push_arrow_skolems env universals domain codomain =
    let (env, skolems) = push_skolems env universals in
    let substitution = Vector.map (fun ov -> T.Ov ov) skolems in
    ( env, skolems
    , Ior.bimap (expose env substitution)
        (fun {T.edomain; eff} ->
            { T.edomain = expose env substitution edomain
            ; eff =  expose env substitution eff })
        domain
    , expose env substitution codomain )

let instantiate_abs env existentials body =
    let uvs = Vector1.map (uv env) existentials in
    let substitution = uvs |> Vector1.to_vector |> Vector.map (fun uv -> T.Uv uv) in
    (uvs, expose env substitution body)

let instantiate_arrow env universals domain codomain =
    let uvs = Vector.map (uv env) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , Ior.bimap (expose env substitution)
        (fun {T.edomain; eff} ->
            {T.edomain = expose env substitution edomain; eff = expose env substitution eff})
        domain
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
    , Vector.map (expose env substitution) codomain )

let find (env : t) pos name =
    let rec find scopes = match scopes with
        | Val var :: scopes -> if var.name = name then var else find scopes
        | Vals (bindings, fields) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some (var, binding) ->
                (match !binding with
                | White (semiabs, expr) ->
                    let env = {env with scopes} in
                    TxRef.set env.tx_log binding Grey;
                    let typing = C.implement env semiabs expr in
                    TxRef.set env.tx_log binding (Black typing);
                    TxRef.set env.tx_log fields (var :: !fields)
                | Grey -> () (* TODO: really? *)
                | Black _ -> ());
                var 
            | None -> find scopes')
        | Row (bindings, fields) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some (var, binding) ->
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
                var
            | None -> find scopes')
        | (Hoisting _ | Rigid _ | Axiom _) :: scopes -> find scopes
        | [] ->
            reportError env pos (Unbound name);
            E.fresh_var (T.Uv (uv env (Uv (uv env T.aKind)))) in
    find env.scopes

let find_rhs (env : t) pos name =
    let rec find scopes = match scopes with
        | Val {name = name'; _} :: scopes ->
            if name' = name
            then failwith "compiler bug: `Env.find_rhs` found `Val` scope"
            else find scopes
        | Vals (bindings, fields) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some (var, binding) ->
                (match !binding with
                | White (semiabs, expr) ->
                    let env = {env with scopes} in
                    TxRef.set env.tx_log binding Grey;
                    let typing = C.implement env semiabs expr in
                    TxRef.set env.tx_log binding (Black typing);
                    TxRef.set env.tx_log fields (var :: !fields);
                    typing
                | Grey -> failwith "compiler bug: `Env.find_rlhs` found `Grey` binding"
                | Black typing -> typing)
            | None -> find scopes')
        | Row (bindings, _) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some _ -> failwith "compiler bug: `Env.find_rhs` found `Row` scope."
            | None -> find scopes')
        | (Hoisting _ | Rigid _ | Axiom _) :: scopes -> find scopes
        | [] ->
            reportError env pos (Unbound name);
            failwith "TODO: find_rhs unbound lie" in
    find env.scopes

let find_rhst (env : t) pos name =
    let rec find scopes = match scopes with
        | Val {name = name'; _} :: scopes ->
            if name' = name
            then failwith "compiler bug: `Env.find_rhst` found `Val` scope"
            else find scopes
        | Vals (bindings, _) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some _ -> failwith "compiler bug: `Env.find_rhst` found `Vals` scope."
            | None -> find scopes')
        | Row (bindings, fields) :: scopes' -> (match Name.Map.find_opt name bindings with
            | Some (var, binding) ->
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
                | GreyT -> failwith "compiler bug: `Env.find_rhst` found `GreyT` binding"
                | BlackT kinding -> kinding)
            | None -> find scopes')
        | (Hoisting _ | Rigid _ | Axiom _) :: scopes -> find scopes
        | [] ->
            reportError env pos (Unbound name);
            failwith "TODO: find_rhst unbound lie" in
    find env.scopes

end

