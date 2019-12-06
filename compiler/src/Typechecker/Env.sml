signature TYPECHECKING_ENV = sig
    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type type_id = FType.Id.t
    type kind = FType.kind
    type odef = FType.def
    type effect = FType.effect

    type 'otyp abs_ctx = 'otyp vector 

    type 't subst = ({name : Name.t, kind : kind, scope : ScopeId.t}, 't) UnionFind.pool

    structure Bindings: sig
        structure TypeFn: sig
            type bindings
        end

        structure Type: sig
            type bindings

            val new: unit -> bindings
            val fromDefs: odef vector1 -> bindings
            val fresh: bindings -> kind -> type_id
            val defs: bindings -> odef list
        end

        structure Expr: sig
            type 'otyp def = {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'otyp}

            datatype ('otyp, 'oexpr) binding_state
                = Unvisited of input_type option def * input_expr option
                | Visiting of input_type option def * input_expr option
                | Typed of ('otyp * 'otyp abs_ctx option) def * input_expr option
                | Visited of 'otyp def * (effect * 'oexpr) option

            type ('otyp, 'oexpr) bindings

            structure Builder: sig
                type ('otyp, 'oexpr) t

                val new: unit -> ('otyp, 'oexpr) t
                val insert: ('otyp, 'oexpr) t -> Pos.span -> Name.t -> ('otyp, 'oexpr) binding_state
                    -> (Pos.span * Name.t, unit) Either.t
                val build: ('otyp, 'oexpr) t -> ('otyp, 'oexpr) bindings
            end
        end
    end

    structure Scope: sig
        structure Id: ID where type t = ScopeId.t

        type ('otyp, 'oexpr) toplevel = { typeFns: Bindings.TypeFn.bindings
                                        , pureCallsite: odef
                                        , vals: ('otyp, 'oexpr) Bindings.Expr.bindings
                                        , subst: 'otyp subst ref }

        datatype ('otyp, 'oexpr) t
            = TopScope of Id.t * ('otyp, 'oexpr) toplevel
            | FnScope of Id.t * Name.t * ('otyp, 'oexpr) Bindings.Expr.binding_state
            | PatternScope of Id.t * Name.t * ('otyp, 'oexpr) Bindings.Expr.binding_state
            | ForAllScope of Id.t * Bindings.Type.bindings
            | ExistsScope of Id.t * Bindings.Type.bindings
            | BlockScope of Id.t * ('otyp, 'oexpr) Bindings.Expr.bindings
            | InterfaceScope of Id.t * ('otyp, 'oexpr) Bindings.Expr.bindings
            | Marker of Id.t

        val id : ('otyp, 'oexpr) t -> Id.t
    end

    type ('otyp, 'oexpr, 'error) t

    val default: Pos.sourcemap -> ('otyp, 'oexpr, 'error) t
    val initial: Pos.sourcemap -> Scope.Id.t * ('otyp, 'oexpr) Scope.toplevel -> ('otyp, 'oexpr, 'error) t
    val innermostScope: ('otyp, 'oexpr, 'error) t -> ('otyp, 'oexpr) Scope.t
    val pushScope: ('otyp, 'oexpr, 'error) t -> ('otyp, 'oexpr) Scope.t -> ('otyp, 'oexpr, 'error) t
    val hasScope: ('otyp, 'oexpr, 'error) t -> Scope.Id.t -> bool

    val findType: ('otyp, 'oexpr, 'error) t -> type_id -> kind option
    val existentialParams: ('otyp, 'oexpr, 'error) t -> odef vector
    val universalParams: ('otyp, 'oexpr, 'error) t -> odef vector
    val nearestExists: ('otyp, 'oexpr, 'error) t -> (Scope.Id.t * Bindings.Type.bindings) option

    val pureCallsite: ('otyp, 'oexpr, 'error) t -> odef
    val freshAbstract: ('otyp, 'oexpr, 'error) t -> kind -> odef
    val typeFns: ('otyp, 'oexpr, 'error) t -> odef vector
   
    val findExpr: ('otyp, 'oexpr, 'error) t -> Name.t -> ('otyp, 'oexpr) Bindings.Expr.binding_state option
    val findExprClosure: ('otyp, 'oexpr, 'error) t -> Name.t
        -> (('otyp, 'oexpr) Bindings.Expr.binding_state * ('otyp, 'oexpr, 'error) t) option
    val updateExpr: Pos.span -> ('otyp, 'oexpr, 'error) t -> Name.t
                  -> (('otyp, 'oexpr) Bindings.Expr.binding_state -> ('otyp, 'oexpr) Bindings.Expr.binding_state)
                  -> (Pos.span * Name.t, unit) Either.t

    val currentSubstitution : ('otyp, 'oexpr, 'error) t -> 'otyp subst
    val setSubstitution : ('otyp, 'oexpr, 'error) t -> 'otyp subst -> unit

    val sourcemap : ('otyp, 'oexpr, 'error) t -> Pos.sourcemap
    val error: ('otyp, 'oexpr, 'error) t -> 'error -> unit
    val errors: ('otyp, 'oexpr, 'error) t -> 'error list
end

structure TypecheckingEnv :> TYPECHECKING_ENV = struct
    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type type_id = FType.Id.t
    type kind = FType.kind
    type odef = FType.def
    type effect = FType.effect

    type 'otyp abs_ctx = 'otyp vector 

    val op|> = Fn.|>

    type 't subst = ({name : Name.t, kind : kind, scope : ScopeId.t}, 't) UnionFind.pool

    structure Bindings = struct
        structure TypeFn = struct
            type bindings = odef list ref

            fun new () = ref []
            fun insert typeFns f = typeFns := f :: !typeFns
            fun freshAbstract typeFns kind =
                let val def = {var = FType.Id.fresh (), kind}
                in insert typeFns def
                 ; def
                end
            val toVector = Vector.fromList o op!
        end

        structure Type = struct
            structure Id = FType.Id

            type binding = kind
            type bindings = binding Id.HashTable.hash_table
            
            val find = Id.HashTable.find

            fun fresh bs kind =
                let val id = Id.fresh ()
                in Id.HashTable.insert bs (id, kind)
                 ; id
                end

            fun new () = Id.HashTable.mkTable (0, Subscript)

            fun fromDefs defs =
                let val bs = new ()
                in Vector1.app (fn {var, kind} => Id.HashTable.insert bs (var, kind)) defs
                 ; bs
                end

            fun defs bs = Id.HashTable.listItemsi bs |> List.map (fn (var, kind) => {var, kind})
        end

        structure Expr = struct
            type 'otyp def = {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'otyp}

            datatype ('otyp, 'oexpr) binding_state
                = Unvisited of input_type option def * input_expr option
                | Visiting of input_type option def * input_expr option
                | Typed of ('otyp * 'otyp abs_ctx option) def * input_expr option
                | Visited of 'otyp def * (effect * 'oexpr) option

            type ('otyp, 'oexpr) bindings = ('otyp, 'oexpr) binding_state NameHashTable.hash_table

            val find = NameHashTable.find

            structure Builder = struct
                type ('otyp, 'oexpr) t = ('otyp, 'oexpr) bindings

                fun new () = NameHashTable.mkTable (0, Subscript)
                fun insert builder pos name b =
                    if NameHashTable.inDomain builder name
                    then Either.Left (pos, name)
                    else Either.Right (NameHashTable.insert builder (name, b))
                val build = Fn.identity
            end
        end
    end

    structure Scope = struct
        structure Id = ScopeId

        type ('otyp, 'oexpr) toplevel = { typeFns: Bindings.TypeFn.bindings
                                        , pureCallsite: odef
                                        , vals: ('otyp, 'oexpr) Bindings.Expr.bindings
                                        , subst: 'otyp subst ref }

        fun initialToplevel () =
            let val typeFns = Bindings.TypeFn.new ()
            in { typeFns
               , pureCallsite = Bindings.TypeFn.freshAbstract typeFns Kind.CallsiteK
               , vals = Bindings.Expr.Builder.new () |> Bindings.Expr.Builder.build
               , subst = ref (UnionFind.pool ()) }
            end

        fun pureCallsite ({pureCallsite, ...}: ('otyp, 'oexpr) toplevel) = pureCallsite

        fun freshAbstract ({typeFns, ...}: ('otyp, 'oexpr) toplevel) kind =
            Bindings.TypeFn.freshAbstract typeFns kind

        fun typeFns ({typeFns, ...}: ('otyp, 'oexpr) toplevel) = Bindings.TypeFn.toVector typeFns

        datatype ('otyp, 'oexpr) t
            = TopScope of Id.t * ('otyp, 'oexpr) toplevel
            | FnScope of Id.t * Name.t * ('otyp, 'oexpr) Bindings.Expr.binding_state
            | PatternScope of Id.t * Name.t * ('otyp, 'oexpr) Bindings.Expr.binding_state
            | ForAllScope of Id.t * Bindings.Type.bindings
            | ExistsScope of Id.t * Bindings.Type.bindings
            | BlockScope of Id.t * ('otyp, 'oexpr) Bindings.Expr.bindings
            | InterfaceScope of Id.t * ('otyp, 'oexpr) Bindings.Expr.bindings
            | Marker of Id.t

        val id = fn FnScope (id, _, _) => id
                  | PatternScope (id, _, _) => id
                  | ForAllScope (id, _) => id
                  | ExistsScope (id, _) => id
                  | BlockScope (id, _) => id
                  | InterfaceScope (id, _) => id
                  | Marker id => id

        val existentialParams =
            fn ExistsScope (_, bindings) =>
                Vector.fromList (Bindings.Type.defs bindings)
             | TopScope _ | FnScope _ | PatternScope _ | ForAllScope _
             | BlockScope _ | InterfaceScope _ | Marker _ => #[]

        val universalParams =
            fn ForAllScope (_, bindings) =>
                Vector.fromList (Bindings.Type.defs bindings)
             | TopScope _ | FnScope _ | PatternScope _ | ExistsScope _
             | BlockScope _ | InterfaceScope _ | Marker _ => #[]

        fun findType scope id =
            case scope
            of ForAllScope (_, bindings) | ExistsScope (_, bindings) => Bindings.Type.find bindings id
             | TopScope _ | FnScope _ | PatternScope _ | BlockScope _ | InterfaceScope _ | Marker _ => NONE

        fun findExpr scope name =
            case scope
            of TopScope (_, {vals, ...}) => Bindings.Expr.find vals name
             | FnScope (_, var, bs) | PatternScope (_, var, bs) => if var = name then SOME bs else NONE
             | ForAllScope _ | ExistsScope _ | Marker _ => NONE
             | BlockScope (_, bindings) | InterfaceScope (_, bindings) => Bindings.Expr.find bindings name
    end

    type ('otyp, 'oexpr, 'error) t =
        { toplevel: ('otyp, 'oexpr) Scope.toplevel
        , scopeIds: Scope.Id.t list
        , scopes: ('otyp, 'oexpr) Scope.t list
        , sourcemap: Pos.sourcemap
        , errors: 'error list ref }
    
    fun initial sourcemap (id, toplevel) =
        { toplevel, scopeIds = [id], scopes = [Scope.TopScope (id, toplevel)]
        , sourcemap, errors = ref []}

    fun default sourcemap = initial sourcemap (Scope.Id.fresh (), Scope.initialToplevel ())

    fun innermostScope ({scopes, ...}: ('otyp, 'oexpr, 'error) t) = hd scopes

    fun pushScope {scopeIds, scopes, toplevel, sourcemap, errors} scope =
        { scopes = scope :: scopes, scopeIds = Scope.id scope :: scopeIds, toplevel
        , sourcemap, errors }

    fun hasScope (env: ('otyp, 'oexpr, 'error) t) id =
        List.exists (fn id' => id' = id) (#scopeIds env)

    fun findType (env: ('otyp, 'oexpr, 'error) t) id =
        let val rec find =
                fn scope :: env =>
                    Scope.findType scope id |> Option.orElse (fn () => find env)
                 | [] => NONE
        in find (#scopes env)
        end

    fun existentialParams ({scopes, ...}: ('otyp, 'oexpr, 'error) t) =
        Vector.concat (List.map Scope.existentialParams scopes)

    fun universalParams ({scopes, ...}: ('otyp, 'oexpr, 'error) t) =
        Vector.concat (List.map Scope.universalParams scopes)

    fun nearestExists ({scopes, ...}: ('otyp, 'oexpr, 'error) t) =
        List.some (fn Scope.ExistsScope scope => SOME scope | _ => NONE) scopes

    fun pureCallsite ({toplevel, ...}: ('otyp, 'oexpr, 'error) t) = Scope.pureCallsite toplevel

    fun freshAbstract ({toplevel, ...}: ('otyp, 'oexpr, 'error) t) kindSig =
        Scope.freshAbstract toplevel kindSig

    fun typeFns ({toplevel, ...}: ('otyp, 'oexpr, 'error) t) = Scope.typeFns toplevel

    fun findExprClosure (env: ('otyp, 'oexpr, 'error) t) name =
        let val rec find =
                fn env as {scopes = scope :: scopes, scopeIds = _ :: scopeIds, toplevel, sourcemap, errors} =>
                    (case Scope.findExpr scope name
                     of SOME b => SOME (b, env)
                      | NONE => find {scopes, scopeIds, toplevel, sourcemap, errors})
                 | {scopes = [], scopeIds = [], ...} => NONE
        in find env
        end

    fun findExpr env name = Option.map #1 (findExprClosure env name)

    fun updateExpr pos (env: ('otyp, 'oexpr, 'error) t) name f =
        let val rec update =
                fn (Scope.BlockScope (_, bs) | Scope.InterfaceScope (_, bs)) :: env =>
                    (case Bindings.Expr.find bs name
                     of SOME v => Either.Right (NameHashTable.insert bs (name, f v))
                      | NONE => update env)
                 | Scope.FnScope (_, var, _) :: env =>
                    if var = name
                    then raise Fail "unreachable"
                    else update env
                 | (Scope.ForAllScope _ | Scope.ExistsScope _) :: env => update env
                 | [] => Either.Left (pos, name)
        in update (#scopes env)
        end

    fun currentSubstitution ({toplevel, ...}: ('otyp, 'oexpr, 'error) t) =
        !(#subst toplevel)

    fun setSubstitution ({toplevel, ...}: ('otyp, 'oexpr, 'error) t) subst' =
        #subst toplevel := subst'

    val sourcemap: ('otyp, 'oexpr, 'error) t -> Pos.sourcemap = #sourcemap

    fun error ({errors, ...}: ('otyp, 'oexpr, 'error) t) err = errors := err :: (!errors)

    fun errors ({errors, ...}: ('otyp, 'oexpr, 'error) t) = List.rev (!errors)
end

