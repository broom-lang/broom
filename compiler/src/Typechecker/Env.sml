signature TYPECHECKING_ENV = sig
    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type output_type = FlexFAst.Type.concr
    type kind = FlexFAst.Type.kind
    type abs_ctx = output_type vector 
    type effect = FlexFAst.Type.effect
    type output_expr = FlexFAst.Term.expr

    structure Bindings: sig
        structure TypeFn: sig
            type bindings
        end

        structure Type: sig
            type binding = kind
            type bindings

            val new: unit -> bindings
            val fromDefs: FlexFAst.Type.def vector1 -> bindings
            val fresh: bindings -> binding -> FType.Id.t
            val defs: bindings -> FlexFAst.Type.def list
        end

        structure Expr: sig
            type 'typ def = {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'typ}

            datatype binding_state
                = Unvisited of input_type option def * input_expr option
                | Visiting of input_type option def * input_expr option
                | Typed of (output_type * abs_ctx option) def * input_expr option
                | Visited of output_type def * (effect * output_expr) option

            type bindings

            structure Builder: sig
                type t

                val new: unit -> t
                val insert: t -> Pos.span -> Name.t -> binding_state -> unit
                val build: t -> bindings
            end
        end
    end

    structure Scope: sig
        structure Id: ID where type t = FlexFAst.ScopeId.t

        type toplevel = { typeFns: Bindings.TypeFn.bindings
                        , pureCallsite: FlexFAst.Type.def
                        , vals: Bindings.Expr.bindings }

        datatype t = TopScope of Id.t * toplevel
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

    val findType: t -> FType.Id.t -> Bindings.Type.binding option
    val universalParams: t -> FlexFAst.Type.def vector
    val nearestExists: t -> (Scope.Id.t * Bindings.Type.bindings) option
    val newUv: t -> Name.t * kind -> FlexFAst.Type.uv
    val freshUv: t -> kind -> FlexFAst.Type.uv

    val pureCallsite: t -> FlexFAst.Type.def
    val freshAbstract: t -> kind -> FlexFAst.Type.def
    val typeFns: t -> FlexFAst.Type.def vector
   
    val findExpr: t -> Name.t -> Bindings.Expr.binding_state option
    val findExprClosure: t -> Name.t -> (Bindings.Expr.binding_state * t) option
    val updateExpr: Pos.span -> t -> Name.t
                  -> (Bindings.Expr.binding_state -> Bindings.Expr.binding_state) -> unit

    val sourcemap : t -> Pos.sourcemap
    val error: t -> TypeError.t -> unit
    val errors: t -> TypeError.t list
end

structure TypecheckingEnv :> TYPECHECKING_ENV = struct
    open TypeError
    structure FAst = FlexFAst

    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type output_type = FAst.Type.concr
    type kind = FlexFAst.Type.kind
    type abs_ctx = output_type vector 
    type effect = FlexFAst.Type.effect
    type output_expr = FAst.Term.expr

    val op|> = Fn.|>

    structure Bindings = struct
        structure TypeFn = struct
            type bindings = FAst.Type.def list ref

            fun new () = ref []
            fun insert typeFns f = typeFns := f :: !typeFns
            fun freshAbstract typeFns kind =
                let val def = {var = FAst.Type.Id.fresh (), kind}
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
                | Typed of (output_type * abs_ctx option) def * input_expr option
                | Visited of output_type def * (effect * output_expr) option

            type bindings = binding_state NameHashTable.hash_table

            val find = NameHashTable.find

            structure Builder = struct
                type t = bindings

                fun new () = NameHashTable.mkTable (0, Subscript)
                fun insert builder pos name b =
                    if NameHashTable.inDomain builder name
                    then raise TypeError (DuplicateBinding (pos, name))
                    else NameHashTable.insert builder (name, b)
                val build = Fn.identity
            end
        end
    end

    structure Scope = struct
        structure Id = FAst.ScopeId

        type toplevel = { typeFns: Bindings.TypeFn.bindings
                        , pureCallsite: FAst.Type.def
                        , vals: Bindings.Expr.bindings }

        fun initialToplevel () =
            let val typeFns = Bindings.TypeFn.new ()
            in { typeFns
               , pureCallsite = Bindings.TypeFn.freshAbstract typeFns FAst.Type.CallsiteK
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
             , errors: TypeError.t list ref }
    
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

    fun newUv (env: t) (name, kind) =
        case #scopes env
        of scope :: _ => TypeVars.Uv.new (Scope.id scope, name, kind)
         | [] => raise Fail "unreachable"

    fun freshUv (env: t) kind =
        case #scopes env
        of scope :: _ => TypeVars.Uv.fresh (Scope.id scope, kind)
         | [] => raise Fail "unreachable"

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
                     of SOME v => NameHashTable.insert bs (name, f v)
                      | NONE => update env)
                 | Scope.FnScope (_, var, _) :: env =>
                    if var = name
                    then raise Fail "unreachable"
                    else update env
                 | (Scope.ForAllScope _ | Scope.ExistsScope _) :: env => update env
                 | [] =>  raise TypeError (UnboundVal (pos, name))
        in update (#scopes env)
        end

    val sourcemap: t -> Pos.sourcemap = #sourcemap

    fun error ({errors, ...}: t) err = errors := err :: (!errors)

    val errors: t -> TypeError.t list = List.rev o op! o #errors
end

