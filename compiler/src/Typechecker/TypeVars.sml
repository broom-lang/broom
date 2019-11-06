structure TypeVars :> sig
    type kind = FType.kind

    exception SetPrivate of Name.t
    exception Reset

    type ov

    structure Ov: sig
        val new: ScopeId.t * Name.t * kind -> ov
        val scope: ov -> ScopeId.t
        val name: ov -> Name.t
    end

    type 't uv

    structure Uv: sig
        val new: ScopeId.t * Name.t * kind -> 't uv
        val fresh: ScopeId.t * kind -> 't uv
        val freshSibling: 't uv -> 't uv
        val get: 't uv -> ('t uv, 't) Either.t
        val merge : (ScopeId.t * ScopeId.t -> order) (* scope ordering to preserve scoping invariants *)
            -> (ScopeId.t -> bool) (* Is the required scope available? *)
            -> 't uv * 't uv -> 't uv
        val set: ('t -> 't uv option) (* Try to unwrap another uv from provided 't. *)
                 -> (ScopeId.t * ScopeId.t -> order) (* scope ordering to preserve scoping invariants *)
                 -> (ScopeId.t -> bool) (* Is the required scope available? *)
                 -> 't uv * 't -> unit
        val eq: 't uv * 't uv -> bool
        val kind : 't uv -> kind
        val name: 't uv -> Name.t
    end

    type 't path

    structure Path: sig
        val new: kind * 't -> 't path
        val face: 't path -> 't
        val get: (ScopeId.t -> bool) (* Is the required coercion available? *)
                 -> 't path -> ('t * Name.t option, (FType.def vector * 't) * Name.t) Either.t
        val addScope: 't path * ScopeId.t * Name.t -> unit
        val set: ('t -> Name.t)
                 -> (ScopeId.t -> bool) (* Is the required coercion available? *)
                 -> 't path * (FType.def vector * 't) -> unit
        val eq: 't path * 't path -> bool
        val kind : 't path -> kind
    end
end = struct
    type kind = FType.kind

    exception SetPrivate of Name.t
    exception Reset

    type meta = {name: Name.t, scope: ScopeId.t, kind: kind}

    type ov = meta

    structure Ov = struct
        fun new (scope, name, kind) = {name, scope, kind}

        val scope: ov -> ScopeId.t = #scope

        val name: ov -> Name.t = #name
    end

    datatype 't link
        = Link of 't uv
        | Root of {meta: meta, typ: 't option ref, rank: int ref}
    withtype 't uv = 't link ref

    structure Uv = struct
        fun new (scope, name, kind) =
            ref (Root { meta = {name, scope, kind}
                      , typ = ref NONE
                      , rank = ref 0 })

        fun fresh (scope, kind) = new (scope, Name.fresh (), kind)

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

        fun freshSibling uv =
            let val meta = #meta (root uv)
            in fresh (#scope meta, #kind meta)
            end

        fun get uv =
            let val uv = find uv
            in case !uv
               of Root {typ, ...} => (case !typ
                                      of SOME t => Either.Right t
                                       | NONE => Either.Left uv)
                | Link _ => raise Fail "unreachable"
            end

        fun assign inScope (uv, t) =
            let val {meta = {scope, name, ...}, typ, ...} = root uv
            in if inScope scope
               then case !typ
                    of SOME _ => raise Reset
                     | NONE => typ := SOME t
               else raise SetPrivate name
            end

        fun newRank (rank, rank') =
            if rank = rank'
            then rank + 1
            else Int.max (rank, rank')

        fun merge scopeCmp inScope (uv, uv') =
            let val uv = find uv
                val uv' = find uv'
            in if uv = uv'
               then uv
               else case (!uv, !uv')
                    of ( Root {meta = {scope, name, kind = _}, rank, ...}
                       , Root { meta = {scope = scope', name = name', kind = _}
                              , rank = rank', ... } ) =>
                        if inScope scope 
                        then if inScope scope'
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
                                   ; parent
                                  end
                            else raise SetPrivate name'
                        else raise SetPrivate name
                     | _ => raise Fail "unreachable"
            end

        fun set uvFromT scopeCmp inScope (uv, t) =
            case uvFromT t
            of SOME uv' => ignore (merge scopeCmp inScope (uv, uv'))
             | NONE => assign inScope (uv, t)

        val eq = op=

        fun kind uv = #kind (#meta (root uv))

        fun name uv = #name (#meta (root uv))
    end

    type 't impl = {typ: (FType.def vector * 't) option, coercion: Name.t option}

    type 't path = {kind: kind, face: 't, impls: (ScopeId.t * 't impl) list ref}

    structure Path = struct
        fun new (kind, face) = {kind, face, impls = ref []}

        val face: 't path -> 't = #face

        fun get inScope ({kind = _, face, impls}: 't path) =
            case List.find (inScope o #1) (!impls)
            of SOME (_, {typ = SOME t, coercion}) => Either.Right (t, valOf coercion)
             | SOME (_, {typ = NONE, coercion}) => Either.Left (face, coercion)
             | NONE => Either.Left (face, NONE)

        fun addScope ({kind = _, face, impls}: 't path, scope, coercion) =
            impls := (scope, {typ = NONE, coercion = SOME coercion}) :: !impls

        fun set faceName inScope ({kind = _, face, impls}: 't path, t) =
            let val rec loop =
                    fn (scope, impl as {typ, coercion}) :: impls =>
                        if inScope scope
                        then case typ
                             of SOME _ => raise Reset
                              | NONE => (scope, {typ = SOME t, coercion}) :: impls
                        else (scope, impl) :: loop impls
                     | [] => raise SetPrivate (faceName face)
            in impls := loop (!impls)
            end

        fun eq ({impls, ...}: 't path, {impls = impls', ...}: 't path) =
            impls = impls'

        val kind: 't path -> kind = #kind
   end
end

