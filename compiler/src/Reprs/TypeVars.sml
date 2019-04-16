signature TYPE_VARS = sig
    exception Reset of Name.t
    
    type 'scope ov
    val newOv: 'scope -> Name.t -> 'scope ov
    val ovEq: ('scope * 'scope -> bool) -> 'scope ov * 'scope ov -> bool
    val ovName: 'scope ov -> Name.t
    val ovInScope: ('scope * 'scope -> order) -> ('scope * 'scope ov) -> bool

    type ('scope, 't) uv
    val newUv: 'scope -> Name.t -> ('scope, 't)  uv
    val freshUv: 'scope -> ('scope, 't) uv
    val uvEq: ('scope, 't) uv * ('scope, 't) uv -> bool
    val uvName: ('scope, 't) uv -> Name.t
    val uvInScope: ('scope * 'scope -> order) -> ('scope * ('scope, 'ti) uv) -> bool
    val uvGet: ('scope, 't) uv -> (('scope, 't) uv, 't) Either.t
    val uvSet: ('scope, 't) uv * 't -> unit
    val uvMerge: ('scope * 'scope -> order) -> ('scope, 't) uv * ('scope, 't) uv -> unit
end

structure TypeVars :> TYPE_VARS = struct
    exception Reset of Name.t

    type 'scope var_descr = { name: Name.t, scope: 'scope }

    type 'scope ov = 'scope var_descr

    fun newOv scope name = {scope, name}
   
    fun ovEq scopeEq ({name, scope}, {name = name', scope = scope'}) =
        name = name' andalso scopeEq (scope, scope')
    
    val ovName: 'scope ov -> Name.t = #name

    fun ovInScope scopeCmp (scope, ov: 'scope ov) =
        case scopeCmp (#scope ov, scope)
        of GREATER | EQUAL => true
         | LESS => false
    
    datatype ('scope, 't) uv_link = Root of { descr: 'scope var_descr, typ: 't option ref }
                                  | Link of ('scope, 't) uv
    withtype ('scope, 't) uv = ('scope, 't) uv_link ref

    fun newUv scope name = ref (Root {descr = {scope, name}, typ = ref NONE})

    fun freshUv scope = newUv scope (Name.fresh ())
   
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

    fun uvInScope scopeCmp (scope, uv) =
        case scopeCmp (#scope (#descr (uvRoot uv)), scope)
        of GREATER | EQUAL => true
         | LESS => false

    fun uvGet uv =
        let val uv = uvFind uv
        in case !uv
           of Root {typ, ...} => (case !typ
                                  of SOME t => Either.Right t
                                   | NONE => Either.Left uv)
            | _ => raise Fail "unreachable"
        end

    fun uvSet (uv, t) = #typ (uvRoot uv) := SOME t

    fun uvMerge scopeCmp (uv, uv') =
        let val uv = uvFind uv
            val uv' = uvFind uv'
        in case (!uv, !uv')
           of ( Root {descr = {scope, ...}, ...}
              , Root {descr = {scope = scope', ...}, ...} ) =>
               (case scopeCmp (scope, scope')
                of LESS => uv := Link uv'
                 | GREATER => uv' := Link uv
                 | EQUAL => uv := Link uv') (* OPTIMIZE: Union by rank here? *)
            | _ => raise Fail "unreachable"
        end
end

