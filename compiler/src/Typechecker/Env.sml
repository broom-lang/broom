signature TYPECHECKING_ENV = sig
    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type type_id = FType.Id.t
    type kind = FType.kind
    type odef = FType.def
    type effect = FType.effect
    type otype
    type oexpr
    type error

    type abs_ctx = otype vector 

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
            type 'typ def = {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'typ}

            datatype binding_state
                = Unvisited of input_type option def * input_expr option
                | Visiting of input_type option def * input_expr option
                | Typed of (otype * abs_ctx option) def * input_expr option
                | Visited of otype def * (effect * oexpr) option

            type bindings

            structure Builder: sig
                type t

                val new: unit -> t
                val insert: t -> Pos.span -> Name.t -> binding_state -> (Pos.span * Name.t, unit) Either.t
                val build: t -> bindings
            end
        end
    end

    structure Scope: sig
        structure Id: ID where type t = ScopeId.t

        type toplevel = { typeFns: Bindings.TypeFn.bindings
                        , pureCallsite: odef
                        , vals: Bindings.Expr.bindings }

        datatype t
            = TopScope of Id.t * toplevel
            | FnScope of Id.t * Name.t * Bindings.Expr.binding_state
            | PatternScope of Id.t * Name.t * Bindings.Expr.binding_state
            | ForAllScope of Id.t * Bindings.Type.bindings
            | ExistsScope of Id.t * Bindings.Type.bindings
            | BlockScope of Id.t * Bindings.Expr.bindings
            | InterfaceScope of Id.t * Bindings.Expr.bindings
            | Marker of Id.t

        val id : t -> Id.t
    end

    type t

    val default: Pos.sourcemap -> t
    val initial: Pos.sourcemap -> Scope.Id.t * Scope.toplevel -> t
    val innermostScope: t -> Scope.t
    val pushScope: t -> Scope.t -> t
    val hasScope: t -> Scope.Id.t -> bool

    val findType: t -> type_id -> kind option
    val universalParams: t -> odef vector
    val nearestExists: t -> (Scope.Id.t * Bindings.Type.bindings) option

    val pureCallsite: t -> odef
    val freshAbstract: t -> kind -> odef
    val typeFns: t -> odef vector
   
    val findExpr: t -> Name.t -> Bindings.Expr.binding_state option
    val findExprClosure: t -> Name.t -> (Bindings.Expr.binding_state * t) option
    val updateExpr: Pos.span -> t -> Name.t
                  -> (Bindings.Expr.binding_state -> Bindings.Expr.binding_state)
                  -> (Pos.span * Name.t, unit) Either.t

    val sourcemap : t -> Pos.sourcemap
    val error: t -> error -> unit
    val errors: t -> error list
end

functor TypecheckingEnv (Output : sig
    type typ
    type expr
    type error
end) :> TYPECHECKING_ENV = struct
    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type type_id = FType.Id.t
    type kind = FType.kind
    type odef = FType.def
    type effect = FType.effect
    type otype = Output.typ
    type oexpr = Output.expr
    type error = Output.error

    type abs_ctx = otype vector 

    val op|> = Fn.|>

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
            type 'typ def = {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'typ}

            datatype binding_state
                = Unvisited of input_type option def * input_expr option
                | Visiting of input_type option def * input_expr option
                | Typed of (otype * abs_ctx option) def * input_expr option
                | Visited of otype def * (effect * oexpr) option

            type bindings = binding_state NameHashTable.hash_table

            val find = NameHashTable.find

            structure Builder = struct
                type t = bindings

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

        type toplevel = { typeFns: Bindings.TypeFn.bindings
                        , pureCallsite: odef
                        , vals: Bindings.Expr.bindings }

        fun initialToplevel () =
            let val typeFns = Bindings.TypeFn.new ()
            in { typeFns
               , pureCallsite = Bindings.TypeFn.freshAbstract typeFns FType.CallsiteK
               , vals = Bindings.Expr.Builder.new () |> Bindings.Expr.Builder.build }
            end

        fun pureCallsite ({pureCallsite, ...}: toplevel) = pureCallsite

        fun freshAbstract ({typeFns, ...}: toplevel) kind =
            Bindings.TypeFn.freshAbstract typeFns kind

        fun typeFns ({typeFns, ...}: toplevel) = Bindings.TypeFn.toVector typeFns

        datatype t = TopScope of Id.t * toplevel
                   | FnScope of Id.t * Name.t * Bindings.Expr.binding_state
                   | PatternScope of Id.t * Name.t * Bindings.Expr.binding_state
                   | ForAllScope of Id.t * Bindings.Type.bindings
                   | ExistsScope of Id.t * Bindings.Type.bindings
                   | BlockScope of Id.t * Bindings.Expr.bindings
                   | InterfaceScope of Id.t * Bindings.Expr.bindings
                   | Marker of Id.t

        val id = fn FnScope (id, _, _) => id
                  | PatternScope (id, _, _) => id
                  | ForAllScope (id, _) => id
                  | ExistsScope (id, _) => id
                  | BlockScope (id, _) => id
                  | InterfaceScope (id, _) => id
                  | Marker id => id

        val rec universalParams =
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

    type t = { toplevel: Scope.toplevel
             , scopeIds: Scope.Id.t list
             , scopes: Scope.t list
             , sourcemap: Pos.sourcemap
             , errors: error list ref }
    
    fun initial sourcemap (id, toplevel) =
        { toplevel, scopeIds = [id], scopes = [Scope.TopScope (id, toplevel)]
        , sourcemap, errors = ref []}

    fun default sourcemap = initial sourcemap (Scope.Id.fresh (), Scope.initialToplevel ())

    fun innermostScope ({scopes, ...}: t) = hd scopes

    fun pushScope {scopeIds, scopes, toplevel, sourcemap, errors} scope =
        { scopes = scope :: scopes, scopeIds = Scope.id scope :: scopeIds, toplevel
        , sourcemap, errors }

    fun hasScope (env: t) id =
        List.exists (fn id' => id' = id) (#scopeIds env)

    fun findType (env: t) id =
        let val rec find =
                fn scope :: env =>
                    Scope.findType scope id |> Option.orElse (fn () => find env)
                 | [] => NONE
        in find (#scopes env)
        end

    fun universalParams ({scopes, ...}: t) =
        Vector.concat (List.map Scope.universalParams scopes)

    fun nearestExists ({scopes, ...}: t) =
        List.some (fn Scope.ExistsScope scope => SOME scope | _ => NONE) scopes

    fun pureCallsite ({toplevel, ...}: t) = Scope.pureCallsite toplevel

    fun freshAbstract ({toplevel, ...}: t) kindSig =
        Scope.freshAbstract toplevel kindSig

    fun typeFns ({toplevel, ...}: t) = Scope.typeFns toplevel

    fun findExprClosure (env: t) name =
        let val rec find =
                fn env as {scopes = scope :: scopes, scopeIds = _ :: scopeIds, toplevel, sourcemap, errors} =>
                    (case Scope.findExpr scope name
                     of SOME b => SOME (b, env)
                      | NONE => find {scopes, scopeIds, toplevel, sourcemap, errors})
                 | {scopes = [], scopeIds = [], ...} => NONE
        in find env
        end

    fun findExpr env name = Option.map #1 (findExprClosure env name)

    fun updateExpr pos (env: t) name f =
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

    val sourcemap: t -> Pos.sourcemap = #sourcemap

    fun error ({errors, ...}: t) err = errors := err :: (!errors)

    val errors: t -> error list = List.rev o op! o #errors
end

