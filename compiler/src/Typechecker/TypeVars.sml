structure TypeVars :> sig
    type kind = FType.kind
    type ('otyp, 'oexpr, 'error) env = ('otyp, 'oexpr, 'error) TypecheckingEnv.t

    exception SetPrivate of Name.t
    exception Reset

    type 't uv

    structure Uv: sig
        val new: ('t, 'oexpr, 'error) env -> Name.t * kind -> 't uv
        val fresh: ('t, 'oexpr, 'error) env -> kind -> 't uv
        val freshSibling: ('t, 'oexpr, 'error) env -> 't uv * kind -> 't uv
        val get: ('t, 'oexpr, 'error) env -> 't uv -> ('t uv, 't) Either.t
        val merge : ('t, 'oexpr, 'error) env -> 't uv * 't uv -> unit
        val set: ('t, 'oexpr, 'error) env -> 't uv -> 't -> unit
        val eq: 't uv * 't uv -> bool
        val kind : ('t, 'oexpr, 'error) env -> 't uv -> kind
        val name: ('t, 'oexpr, 'error) env -> 't uv -> Name.t
    end

    type 't path

    structure Path: sig
        val new: kind * 't -> 't path
        val face: 't path -> 't
        val get: ('t, 'oexpr, 'error) env -> 't path -> ('t, 't uv * Name.t) Either.t
        val addScope: ('t, 'expr, 'error) env -> 't path -> ScopeId.t * Name.t -> unit
        val eq: 't path * 't path -> bool
        val kind : 't path -> kind
    end
end = struct
    structure Env = TypecheckingEnv
    type kind = FType.kind
    type ('otyp, 'oexpr, 'error) env = ('otyp, 'oexpr, 'error) Env.t

    val rec kindCodomain =
      fn FType.ArrowK {codomain, ...} => kindCodomain codomain
       | kind => kind

    exception SetPrivate of Name.t
    exception Reset

    type meta = {name: Name.t, scope: ScopeId.t, kind: kind}

    type 't uv = (meta, 't) UnionFind.t

    structure Uv = struct
        fun make env meta =
            let val subst = Env.currentSubstitution env
                val (uv, subst') = UnionFind.new subst meta
            in Env.setSubstitution env subst'
             ; uv
            end

        fun new env (name, kind) =
            let val scope = Env.Scope.id (Env.innermostScope env)
            in make env {name, scope, kind}
            end

        fun fresh env kind = new env (Name.fresh (), kind)

        fun freshSibling env (uv, kind) =
            let val scope = #scope (#1 (UnionFind.get (Env.currentSubstitution env) uv))
            in make env {name = Name.fresh (), scope, kind}
            end

        fun get env uv = #2 (UnionFind.get (Env.currentSubstitution env) uv)

        fun set env uv t =
            let val pool = Env.currentSubstitution env
                val ({scope, name, kind = _}, _) = UnionFind.get (Env.currentSubstitution env) uv
            in if not (Env.hasScope env scope)
               then raise SetPrivate name
               else case UnionFind.define pool uv t
                    of Either.Left _ => raise Reset
                     | Either.Right pool' => Env.setSubstitution env pool'
            end

        fun compareMetaScopes ({scope, ...}: meta, {scope = scope', ...}: meta) =
            Env.Scope.Id.compare (scope, scope')

        fun merge env (uv, uv') =
            let val subst = Env.currentSubstitution env
                val ({scope, name, ...}, _) = UnionFind.get subst uv
            in if not (Env.hasScope env scope)
               then raise SetPrivate name
               else let val ({scope, name, ...}, _) = UnionFind.get subst uv'
                    in if not (Env.hasScope env scope)
                       then raise SetPrivate name
                       else let val subst' = UnionFind.union subst compareMetaScopes (uv, uv')
                            in Env.setSubstitution env subst'
                            end
                    end
            end

        val eq = UnionFind.eq

        fun kind env uv = #kind (#1 (UnionFind.get (Env.currentSubstitution env) uv))
        fun name env uv = #name (#1 (UnionFind.get (Env.currentSubstitution env) uv))
    end

    type 't impl = {typ: 't uv, coercion: Name.t}

    type 't path = {kind: kind, face: 't, impls: (ScopeId.t * 't impl) list ref}

    structure Path = struct
        fun new (kind, face) = {kind, face, impls = ref []}

        val face: 't path -> 't = #face

        fun get env ({kind = _, face, impls}: 't path) =
            case List.find (Env.hasScope env o #1) (!impls)
            of SOME (_, {typ = uv, coercion}) => Either.Right (uv, coercion)
             | NONE => Either.Left face

        fun addScope env ({kind, face = _, impls}: 't path) (scope, coercion) =
            let val uv = Uv.make env {name = Name.fresh (), scope, kind = kindCodomain kind}
            in impls := (scope, {typ = uv, coercion}) :: !impls
            end

        fun eq ({impls, ...}: 't path, {impls = impls', ...}: 't path) =
            impls = impls'

        val kind: 't path -> kind = #kind
   end
end

