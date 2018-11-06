signature TYPE_VARS = sig
    type ov     (* Opaque variable *)
    type 't uv  (* Unification variable *)
    type 't env (* Type variable environment *)

    val newEnv: unit -> 't env

    val pushOv: 't env -> Name.t -> ov
    val popOv: 't env -> ov -> unit

    val pushUv: 't env -> 't uv
    val insertUvBefore: 't env -> 't uv -> 't uv
    val popUv: 't env -> 't uv -> unit
    
    val ovInScope: 't env -> ov -> bool
    val uvInScope: 't env -> 't uv -> bool
    val compareUvScopes: 't env -> 't uv -> 't uv -> order
end
