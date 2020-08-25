module T = Fc.Type

module Bindings = Map.Make(Name)

type uv = Fc.Uv.t

type scope =
    | Hoisting of T.binding list ref * T.level

type t =
    { bindings : Fc.Type.t Bindings.t
    ; uv_subst : Fc.Uv.subst ref
    ; scopes : scope list
    ; level : Fc.Type.level }

let initial_level = 1

let interactive () =
    { bindings = Bindings.empty
    ; uv_subst = ref (Fc.Uv.new_subst ())
    ; scopes = [Hoisting (ref [], initial_level)]
    ; level = initial_level }

let eval () =
    { bindings = Bindings.empty
    ; uv_subst = ref (Fc.Uv.new_subst ())
    ; scopes = [Hoisting (ref [], initial_level)]
    ; level = initial_level }

let add k v (env : t) = {env with bindings = Bindings.add k v env.bindings}

let find k (env : t) = Bindings.find k env.bindings

let generate env binding =
    let rec generate = function
        | Hoisting (bindings, level) :: _ ->
            bindings := binding :: !bindings;
            (binding, level)
        | _ :: scopes' -> generate scopes'
        | [] -> failwith "Typer.Env.generate: missing root Hoisting scope"
    in generate env.scopes

let uv (env : t) name = Fc.Uv.make_r env.uv_subst (Unassigned (name, env.level))

let get_uv (env : t) uv = Fc.Uv.getr env.uv_subst uv

let set_uv (env : t) uv v = Fc.Uv.setr env.uv_subst uv v

let sibling (env : t) uv = match get_uv env uv with
    | Unassigned (_, level) -> Fc.Uv.make_r env.uv_subst (Unassigned (Name.fresh (), level))
    | Assigned _ -> failwith "unreachable"

let uv_substr (env : t) = env.uv_subst

let current_uv_subst (env : t) = ! (env.uv_subst)

