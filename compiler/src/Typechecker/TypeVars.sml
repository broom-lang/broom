signature TYPE_VARS = sig
    exception Reset of Name.t

    datatype predicativity = Predicative | Impredicative
    
    type ('scope, 't) uv
    val newUv: 'scope -> predicativity * Name.t -> ('scope, 't)  uv
    val freshUv: 'scope -> predicativity -> ('scope, 't) uv
    val uvEq: ('scope, 't) uv * ('scope, 't) uv -> bool
    val uvName: ('scope, 't) uv -> Name.t
    val uvScope: ('scope, 't) uv -> 'scope
    val uvInScope: ('scope * 'scope -> order) -> ('scope * ('scope, 'ti) uv) -> bool
    val uvGet: ('scope, 't) uv -> (('scope, 't) uv, 't) Either.t
    val uvSet: ('scope, 't) uv * 't -> unit
    val uvMerge: ('scope * 'scope -> order) -> ('scope, 't) uv * ('scope, 't) uv -> unit
end

structure TypeVars :> TYPE_VARS = struct
    exception Reset of Name.t

    datatype predicativity = Predicative | Impredicative

    type 'scope var_descr = {name: Name.t, scope: 'scope, predicativity: predicativity ref}

    datatype ('scope, 't) uv_link = Root of { descr: 'scope var_descr, typ: 't option ref }
                                  | Link of ('scope, 't) uv
    withtype ('scope, 't) uv = ('scope, 't) uv_link ref

    fun newUv scope (predicativity, name) =
        ref (Root {descr = {scope, name, predicativity = ref predicativity}, typ = ref NONE})

    fun freshUv scope predicativity = newUv scope (predicativity, Name.fresh ())
   
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

    fun uvScope uv = #scope (#descr (uvRoot uv))

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

    fun updatePredicativity outerPredRef innerPred =
        case (!outerPredRef, innerPred)
        of (Impredicative, Predicative) => outerPredRef := Predicative
         | _ => ()

    fun uvMerge scopeCmp (uv, uv') =
        let val uv = uvFind uv
            val uv' = uvFind uv'
        in case (!uv, !uv')
           of ( Root {descr = {scope, predicativity, ...}, ...}
              , Root {descr = {scope = scope', predicativity = predicativity', ...}, ...} ) =>
               (case scopeCmp (scope, scope')
                of LESS => ( uv := Link uv'
                           ; updatePredicativity predicativity' (!predicativity) )
                 | GREATER => ( uv' := Link uv
                              ; updatePredicativity predicativity (!predicativity') )
                 | EQUAL => (* OPTIMIZE: Union by rank here? *)
                    ( uv := Link uv'
                    ; updatePredicativity predicativity' (!predicativity) ))
            | _ => raise Fail "unreachable"
        end
end

