module Bindings = Map.Make(Name)

type t =
    { bindings : Fc.Type.t Bindings.t
    ; uv_subst : Fc.Uv.subst ref }

let interactive () = {bindings = Bindings.empty; uv_subst = ref (Fc.Uv.new_subst ())}

let eval () = {bindings = Bindings.empty; uv_subst = ref (Fc.Uv.new_subst ())}

let add k v (env : t) = {env with bindings = Bindings.add k v env.bindings}

let find k (env : t) = Bindings.find k env.bindings

let current_uv_subst (env : t) = ! (env.uv_subst)

