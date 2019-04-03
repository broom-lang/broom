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

signature SCOPE = sig
    type scope
    val eq: scope * scope -> bool
    val compare: scope * scope -> order
end

functor TypeVarsFn(Scope: SCOPE) :> TYPE_VARS = struct
    type scope = Scope.scope

    exception Reset of Name.t

    type var_descr = { name: Name.t, scope: scope }

    type ov = var_descr
   
    fun ovEq ({name, scope}, {name = name', scope = scope'}) =
        name = name' andalso Scope.eq (scope, scope')
    
    val ovName: ov -> Name.t = #name
    
    datatype 't uv_link = Root of { descr: var_descr, typ: 't option ref }
                        | Link of 't uv
    withtype 't uv = 't uv_link ref
   
    fun uvFind uv =
        case !uv
        of Root _ => uv
         | Link uv' => let val res = uvFind uv'
                       in uv := Link res (* path compression *)
                        ; res
                       end

    fun uvEq (uv, uv') = uvFind uv = uvFind uv'

    fun uvRoot uv =
        case !(uvFind uv)
        of Root root => root
         | _ => raise Fail "unreachable"
   
    fun uvName uv = #name (#descr (uvRoot uv)) 

    fun uvGet uv =
        let val uv = uvFind uv
        in case !uv
           of Root {typ, ...} => (case !typ
                                  of SOME t => Either.Right t
                                   | NONE => Either.Left uv)
            | _ => raise Fail "unreachable"
        end

    fun uvSet (uv, t) = #typ (uvRoot uv) := SOME t

    fun uvMerge (uv, uv') =
        let val uv = uvFind uv
            val uv' = uvFind uv'
        in case (!uv, !uv')
           of ( Root {descr = {scope, ...}, ...}
              , Root {descr = {scope = scope', ...}, ...} ) =>
               (case Scope.compare (scope, scope')
                of LESS => uv := Link uv'
                 | GREATER => uv' := Link uv
                 | EQUAL => uv := Link uv') (* OPTIMIZE: Union by rank here? *)
            | _ => raise Fail "unreachable"
        end
end

