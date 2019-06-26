structure TypeVars :> sig
    datatype predicativity = Predicative | Impredicative

    exception SetPrivate
    exception Reset

    structure Opaque: sig
        type ('scope, 'kind) ov

        val new: 'scope * predicativity * Name.t * 'kind -> ('scope, 'kind) ov
    end

    structure Flexible: sig
        type ('scope, 't) uv

        val new: 'scope * predicativity * Name.t -> ('scope, 't) uv
        val get: ('scope, 't) uv -> (('scope, 't) uv, 't) Either.t
        val set: ('t -> ('scope, 't) uv option) (* Try to unwrap another uv from provided 't. *)
                 -> ('scope * 'scope -> order) (* scope ordering to preserve scoping invariants *)
                 -> ('scope -> bool) (* Is the required scope available? *)
                 -> ('scope, 't) uv * 't -> unit
    end

    structure Path: sig
        type ('co, 't) path

        val new: 't * 'co -> ('co, 't) path
        val get: ('co -> bool) (* Is the required coercion available? *)
                 -> ('co, 't) path -> ('t, 't * 'co) Either.t
        val set: ('co -> bool) (* Is the required coercion available? *)
                 -> ('co, 't) path * 't -> unit
    end
end = struct
    datatype predicativity = Predicative | Impredicative

    exception SetPrivate
    exception Reset

    type 'scope meta = { name: Name.t
                   , scope: 'scope
                   , predicativity: predicativity }

    structure Opaque = struct
        type ('scope, 'kind) ov = {meta: 'scope meta, kind: 'kind}

        fun new (scope, predicativity, name, kind) =
            {meta = {name, scope, predicativity}, kind}
    end

    structure Flexible = struct
        datatype ('scope, 't) link
            = Link of ('scope, 't) uv
            | Root of {meta: 'scope meta, typ: 't option ref, rank: int ref}

        withtype ('scope, 't) uv = ('scope, 't) link ref

        fun new (scope, predicativity, name) =
            ref (Root { meta = {name, scope, predicativity}
                      , typ = ref NONE
                      , rank = ref 0 })

        fun find uv =
            case !uv
            of Link uv' => let val res = find uv'
                           in uv := Link res (* path compression *)
                            ; res
                           end
             | Root _ => uv

        fun root uv =
            case !(find uv)
            of Root root => root
             | Link _ => raise Fail "unreachable"

        fun get uv =
            let val uv = find uv
            in case !uv
               of Root {typ, ...} => (case !typ
                                      of SOME t => Either.Right t
                                       | NONE => Either.Left uv)
                | Link _ => raise Fail "unreachable"
            end

        fun assign inScope (uv, t) =
            let val {meta = {scope, ...}, typ, ...} = root uv
            in if inScope scope
               then case !typ
                    of SOME _ => raise Reset
                     | NONE => typ := SOME t
               else raise SetPrivate
            end

        fun newRank (rank, rank') =
            if rank = rank'
            then rank + 1
            else Int.max (rank, rank')

        fun merge scopeCmp inScope (uv, uv') =
            let val uv = find uv
                val uv' = find uv'
            in if uv = uv'
               then ()
               else case (!uv, !uv')
                    of ( Root {meta = {scope, predicativity, ...}, rank, ...}
                       , Root {meta = {scope = scope', predicativity = predicativity', ...}, rank = rank', ...} ) =>
                        if inScope scope andalso inScope scope'
                        then let val (child, parent, parentRank) =
                                     case scopeCmp (scope, scope')
                                     of LESS => (uv, uv', rank')
                                      | GREATER => (uv', uv, rank)
                                      | EQUAL => (case Int.compare (!rank, !rank')
                                                  of LESS => (uv, uv', rank')
                                                   | GREATER => (uv', uv, rank)
                                                   | EQUAL => (uv, uv', rank'))
                             in child := Link parent
                              ; parentRank := newRank (!rank, !rank')
                             end
                        else raise SetPrivate
                     | _ => raise Fail "unreachable"
            end

        fun set uvFromT scopeCmp inScope (uv, t) =
            case uvFromT t
            of SOME uv' => merge scopeCmp inScope (uv, uv')
             | NONE => assign inScope (uv, t)
    end

    structure Path = struct
        type ('co, 't) path = {face: 't, coercion: 'co, impl: 't option ref}

        fun new (face, coercion) = {face, coercion, impl = ref NONE}

        fun get inScope {face, coercion, impl} =
            if inScope coercion
            then case !impl
                 of SOME t => Either.Right (t, coercion)
                  | NONE => Either.Left face
            else Either.Left face

        fun set inScope ({face = _, coercion, impl}, t) =
            if inScope coercion
            then case !impl
                 of SOME _ => raise Reset
                  | NONE => impl := SOME t
            else raise SetPrivate
   end
end

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

