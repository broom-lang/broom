module Bindings = Map.Make(Name)

type t =
    { bindings : FcType.t Bindings.t
    ; uv_subst : FcType.uvv FcType.Uv.store ref }

let interactive () = {bindings = Bindings.empty; uv_subst = ref (FcType.Uv.new_store ())}

let eval () = {bindings = Bindings.empty; uv_subst = ref (FcType.Uv.new_store ())}

let add k v (env : t) = {env with bindings = Bindings.add k v env.bindings}

let find k (env : t) = Bindings.find k env.bindings

let current_uv_subst (env : t) = ! (env.uv_subst)

