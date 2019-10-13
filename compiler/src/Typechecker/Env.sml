structure TypecheckingEnv :> sig
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

        structure Axiom: sig
            type bindings
        end

        structure Type: sig
            type binding = kind
            type bindings

            val new: unit -> bindings
            val fromDefs: FlexFAst.Type.def vector -> bindings
            val fresh: bindings -> binding -> FType.Id.t
            val defs: bindings -> FlexFAst.Type.def list
        end

        structure Expr: sig
            datatype binding_state
                = Unvisited of input_type option * input_expr option
                | Visiting of input_type option * input_expr option
                | Typed of output_type * abs_ctx option * input_expr option
                | Visited of output_type * (effect * output_expr) option

            type bindings

            structure Builder: sig
                type t

                val new: unit -> t
                val insert: t -> Name.t -> binding_state -> unit
                val build: t -> bindings
            end
        end
    end

    structure Scope: sig
        structure Id: ID where type t = FlexFAst.ScopeId.t

        type toplevel = { typeFns: Bindings.TypeFn.bindings
                        , pureCallsite: Name.t
                        , axioms: Bindings.Axiom.bindings
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

    val default: unit -> t
    val initial: Scope.Id.t * Scope.toplevel -> t
    val innermostScope: t -> Scope.t option
    val pushScope: t -> Scope.t -> t
    val hasScope: t -> Scope.Id.t -> bool

    val findType: t -> FType.Id.t -> Bindings.Type.binding option
    val universalParams: t -> FlexFAst.Type.def vector
    val nearestExists: t -> (Scope.Id.t * Bindings.Type.bindings) option
    val newUv: t -> TypeVars.predicativity * Name.t -> FlexFAst.Type.uv
    val freshUv: t -> TypeVars.predicativity -> FlexFAst.Type.uv

    val pureCallsite: t -> Name.t
    val freshAbstract: t -> FlexFAst.Type.Id.t -> FlexFAst.Type.tfn_sig -> Name.t
    val typeFns: t -> (Name.t * FlexFAst.Type.tfn_sig) vector
    val insertAxiom: t -> Name.t -> output_type * output_type -> unit
    val axioms: t -> (Name.t * output_type * output_type) vector 
   
    val findExpr: t -> Name.t -> Bindings.Expr.binding_state option
    val findExprClosure: t -> Name.t -> (Bindings.Expr.binding_state * t) option
    val updateExpr: Pos.t -> t -> Name.t
                  -> (Bindings.Expr.binding_state -> Bindings.Expr.binding_state) -> unit

    val error: t -> TypeError.t -> unit
    val errors: t -> TypeError.t list
end = struct
    open TypeError
    structure FAst = FlexFAst

    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type output_type = FAst.Type.concr
    type kind = FlexFAst.Type.kind
    type tfn_sig = FAst.Type.tfn_sig
    type abs_ctx = output_type vector 
    type effect = FlexFAst.Type.effect
    type output_expr = FAst.Term.expr

    val op|> = Fn.|>

    structure Bindings = struct
        structure TypeFn = struct
            type bindings = tfn_sig NameHashTable.hash_table

            fun new () = NameHashTable.mkTable (0, Subscript)
            val insert = NameHashTable.insert
            fun freshAbstract typeFns id kindSig =
                let val name = "g__" ^ FAst.Type.Id.toString id |> Name.fromString |> Name.freshen
                in insert typeFns (name, kindSig)
                 ; name
                end
            val toVector = Vector.fromList o NameHashTable.listItemsi
        end

        structure Axiom = struct
            type binding = output_type * output_type

            type bindings = binding NameHashTable.hash_table

            fun new () = NameHashTable.mkTable (0, Subscript)
            val insert = NameHashTable.insert
            fun toVector axioms =
                axioms |> NameHashTable.listItemsi |> Vector.fromList
                       |> Vector.map (fn (name, (l, r)) => (name, l, r))
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
                in Vector.app (fn {var, kind} => Id.HashTable.insert bs (var, kind)) defs
                 ; bs
                end

            fun defs bs = Id.HashTable.listItemsi bs |> List.map (fn (var, kind) => {var, kind})
        end

        structure Expr = struct
            datatype binding_state
                = Unvisited of input_type option * input_expr option
                | Visiting of input_type option * input_expr option
                | Typed of output_type * abs_ctx option * input_expr option
                | Visited of output_type * (effect * output_expr) option

            type bindings = binding_state NameHashTable.hash_table

            val find = NameHashTable.find

            structure Builder = struct
                type t = bindings

                fun new () = NameHashTable.mkTable (0, Subscript)
                fun insert builder name b = NameHashTable.insert builder (name, b)
                val build = Fn.identity
            end
        end
    end

    structure Scope = struct
        structure Id = FAst.ScopeId

        type toplevel = { typeFns: Bindings.TypeFn.bindings
                        , pureCallsite: Name.t
                        , axioms: Bindings.Axiom.bindings
                        , vals: Bindings.Expr.bindings }

        fun initialToplevel () =
            let val typeFns = Bindings.TypeFn.new ()
            in { typeFns
               , pureCallsite = Bindings.TypeFn.freshAbstract typeFns (FAst.Type.Id.fresh ())
                                                              {paramKinds = #[], kind = FAst.Type.CallsiteK (Pos.default "<builtin>")}
               , axioms = Bindings.Axiom.new ()
               , vals = Bindings.Expr.Builder.new () |> Bindings.Expr.Builder.build }
            end

        fun pureCallsite ({pureCallsite, ...}: toplevel) = pureCallsite

        fun freshAbstract ({typeFns, ...}: toplevel) id kindSig =
            Bindings.TypeFn.freshAbstract typeFns id kindSig

        fun typeFns ({typeFns, ...}: toplevel) = Bindings.TypeFn.toVector typeFns

        fun insertAxiom ({axioms, ...}: toplevel) name ax =
            Bindings.Axiom.insert axioms (name, ax)

        fun axioms ({axioms, ...}: toplevel) = Bindings.Axiom.toVector axioms

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
             , errors: TypeError.t list ref }
    
    fun initial (id, toplevel) =
        {toplevel, scopeIds = [id], scopes = [Scope.TopScope (id, toplevel)], errors = ref []}

    fun default () = initial (Scope.Id.fresh (), Scope.initialToplevel ())

    fun innermostScope ({scopes, ...}: t) =
        case scopes
        of scope :: _ => SOME scope
         | [] => NONE

    fun pushScope {scopeIds, scopes, toplevel, errors} scope =
        {scopes = scope :: scopes, scopeIds = Scope.id scope :: scopeIds, toplevel, errors}

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

    fun newUv (env: t) (predicativity, name) =
        case #scopes env
        of scope :: _ => TypeVars.Uv.new (Scope.id scope, predicativity, name)
         | [] => raise Fail "unreachable"

    fun freshUv (env: t) predicativity =
        case #scopes env
        of scope :: _ => TypeVars.Uv.fresh (Scope.id scope, predicativity)
         | [] => raise Fail "unreachable"

    fun pureCallsite ({toplevel, ...}: t) = Scope.pureCallsite toplevel

    fun freshAbstract ({toplevel, ...}: t) id kindSig =
        Scope.freshAbstract toplevel id kindSig

    fun typeFns ({toplevel, ...}: t) = Scope.typeFns toplevel

    fun insertAxiom ({toplevel, ...}: t) = Scope.insertAxiom toplevel

    fun axioms ({toplevel, ...}: t) = Scope.axioms toplevel

    fun findExprClosure (env: t) name =
        let val rec find =
                fn env as {scopes = scope :: scopes, scopeIds = _ :: scopeIds, toplevel, errors} =>
                    (case Scope.findExpr scope name
                     of SOME b => SOME (b, env)
                      | NONE => find {scopes, scopeIds, toplevel, errors})
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

    fun error ({errors, ...}: t) err = errors := err :: (!errors)

    val errors: t -> TypeError.t list = List.rev o op! o #errors
end

