module T = Fc.Type

val expose_abs : Env.t -> T.t Vector.t -> T.abs -> T.abs
val expose : Env.t -> T.t Vector.t -> T.t -> T.t
val expose_template : Env.t -> T.t Vector.t -> T.template -> T.template

val close_abs : Env.t -> int Name.Map.t -> T.abs -> T.abs
val close : Env.t -> int Name.Map.t -> T.t -> T.t
val close_template : Env.t -> int Name.Map.t -> T.template -> T.template

val reabstract : Env.t -> T.abs -> T.ov Vector.t * T.t
val push_abs_skolems : Env.t -> T.abs -> Env.t * T.ov Vector.t * T.t
val push_arrow_skolems : Env.t -> T.kind Vector.t -> T.t Vector.t -> T.t -> T.abs
    -> Env.t * T.ov Vector.t * T.t Vector.t * T.t * T.abs
val instantiate_abs : Env.t -> T.abs -> T.uv Vector.t * T.t
val instantiate_arrow : Env.t -> T.kind Vector.t -> T.t Vector.t
    -> T.t -> T.abs -> T.uv Vector.t * T.t Vector.t * T.t * T.abs

