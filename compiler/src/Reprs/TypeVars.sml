signature TYPE_VARS = sig
    exception Reset of Name.t
    
    type ov
    val ovEq: ov * ov -> bool
    val ovName: ov -> Name.t

    type 't uv
    val uvEq: 't uv * 't uv -> bool
    val uvName: 't uv -> Name.t
    val uvGet: 't uv -> ('t uv, 't) Either.t
    val uvSet: 't uv * 't -> unit
    val uvMerge: 't uv * 't uv -> unit
end

