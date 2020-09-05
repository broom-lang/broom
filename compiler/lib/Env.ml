module T = Fc.Type

module Bindings = Map.Make(Name)

type uv = Fc.Uv.t

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
        | [] -> failwith "Typer.Env.generate: missing root Hoisting scope"
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

let uv (env : t) name = Fc.Uv.make env.tx_log (Unassigned (name, env.level))

let get_uv (env : t) uv = Fc.Uv.get env.tx_log uv

let set_uv (env : t) uv v = Fc.Uv.set env.tx_log uv v

let sibling (env : t) uv = match get_uv env uv with
    | Unassigned (_, level) -> Fc.Uv.make env.tx_log (Unassigned (Name.fresh (), level))
    | Assigned _ -> failwith "unreachable"

let tx_log (env : t) = env.tx_log

