module Bindings = Map.Make(Name)

type t =
    { bindings : Fc.Type.t Bindings.t
    ; uv_subst : Fc.Uv.subst ref }

let interactive () = {bindings = Bindings.empty; uv_subst = ref (Fc.Uv.new_subst ())}

let eval () = {bindings = Bindings.empty; uv_subst = ref (Fc.Uv.new_subst ())}

let add k v (env : t) = {env with bindings = Bindings.add k v env.bindings}

let find k (env : t) = Bindings.find k env.bindings

let get_uv (env : t) uv = Fc.Uv.getr env.uv_subst uv

let set_uv (env : t) uv v = Fc.Uv.setr env.uv_subst uv v

let uv_substr (env : t) = env.uv_subst

let current_uv_subst (env : t) = ! (env.uv_subst)

