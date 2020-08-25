module T = Fc.Type

let reabstract env (T.Exists (params, locator, body)) =
    let params' = Vector.map (fun kind -> Env.generate env (Name.fresh (), kind)) params in
    let substitution = Vector.map (fun ov -> T.Ov ov) params' in
    ( params'
    , T.expose_locator (Env.uv_substr env) substitution locator
    , T.expose (Env.uv_substr env) substitution body )

let instantiate_abs env (T.Exists (existentials, locator, body)) =
    let uvs = Vector.map (fun _ -> Env.uv env (Name.fresh ())) existentials in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , T.expose_locator (Env.uv_substr env) substitution locator
    , T.expose (Env.uv_substr env) substitution body )

let instantiate_arrow env universals domain_locator domain eff codomain =
    let uvs = Vector.map (fun _ -> Env.uv env (Name.fresh())) universals in
    let substitution = Vector.map (fun uv -> T.Uv uv) uvs in
    ( uvs
    , T.expose_locator (Env.uv_substr env) substitution domain_locator
    , T.expose (Env.uv_substr env) substitution domain, eff
    , T.expose_abs (Env.uv_substr env) substitution codomain )

