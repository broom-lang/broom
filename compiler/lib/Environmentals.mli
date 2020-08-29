module T = Fc.Type

val expose_abs : Env.t -> T.t Vector.t -> T.abs -> T.abs
val expose : Env.t -> T.t Vector.t -> T.t -> T.t
val expose_locator : Env.t -> T.t Vector.t -> T.locator -> T.locator

val close_abs : Env.t -> int Name.Map.t -> T.abs -> T.abs
val close : Env.t -> int Name.Map.t -> T.t -> T.t
val close_locator : Env.t -> int Name.Map.t -> T.locator -> T.locator

val reabstract : Env.t -> T.abs -> T.ov Vector.t * T.locator * T.t
val push_abs_skolems : Env.t -> T.abs -> Env.t * T.ov Vector.t * T.t
val instantiate_abs : Env.t -> T.abs -> T.uv Vector.t * T.locator * T.t
val instantiate_arrow : Env.t -> T.kind Vector.t -> (T.locator * T.t) Vector.t
    -> T.t -> T.abs -> T.uv Vector.t * (T.locator * T.t) Vector.t * T.t * T.abs

