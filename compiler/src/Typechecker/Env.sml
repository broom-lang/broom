structure TypecheckingEnv :> sig
    structure TC: TYPECHECKING where
        type ScopeId.t = TypecheckingCst.ScopeId.t and
        type Output.Type.kind = FType.kind and
        type 'sv Output.Type.concr = 'sv FType.concr and
        type 'sv Output.Term.expr = 'sv FAst.Term.expr and
        type sv = TypecheckingCst.sv

    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type output_type = TC.sv TC.Output.Type.concr
    type output_expr = TC.sv TC.Output.Term.expr

    structure Bindings: sig
        structure Type: sig
            type binding = TC.Output.Type.kind
            type bindings

            val new: unit -> bindings
            val fresh: bindings -> binding -> Id.t
            val defs: bindings -> TC.Output.Type.def list
        end

        structure Expr: sig
            datatype binding_state
                = Unvisited of input_type option * input_expr option
                | Visiting of input_type option * input_expr option
                | Typed of output_type * input_expr option
                | Visited of output_type * output_expr option

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
        structure Id: ID where type t = TC.ScopeId.t

        datatype t = FnScope of Id.t * Name.t * Bindings.Expr.binding_state
                   | ForAllScope of Id.t * TC.Output.Type.def
                   | ExistsScope of Id.t * Bindings.Type.bindings
                   | BlockScope of Id.t * Bindings.Expr.bindings
                   | InterfaceScope of Id.t * Bindings.Expr.bindings
    end

    type t

    val empty: t
    val pushScope: t -> Scope.t -> t

    val findType: t -> Id.t -> Bindings.Type.binding option
    val freshAbstract: t -> Bindings.Type.binding -> Id.t
    val newUv: t -> TypeVars.predicativity * Name.t -> TC.uv
    val freshUv: t -> TypeVars.predicativity -> TC.uv
    val uvInScope: t * TC.uv -> bool
   
    val findExpr: t -> Name.t -> Bindings.Expr.binding_state option
    val findExprClosure: t -> Name.t -> (Bindings.Expr.binding_state * t) option
    val updateExpr: Pos.t -> t -> Name.t
                  -> (Bindings.Expr.binding_state -> Bindings.Expr.binding_state) -> unit
end = struct
    open TypeError
    structure TC = TypecheckingCst

    type input_type = TC.Input.Type.typ
    type input_expr = TC.Input.Term.expr
    type output_type = TC.sv TC.Output.Type.concr
    type output_expr = TC.sv TC.Output.Term.expr

    val op|> = Fn.|>

    structure Bindings = struct
        structure Type = struct
            type binding = TC.Output.Type.kind
            type bindings = binding Id.HashTable.hash_table
            
            val find = Id.HashTable.find

            fun fresh bs kind =
                let val id = Id.fresh ()
                in Id.HashTable.insert bs (id, kind)
                 ; id
                end

            fun new () = Id.HashTable.mkTable (0, Subscript)

            fun defs bs = Id.HashTable.listItemsi bs |> List.map (fn (var, kind) => {var, kind})
        end

        structure Expr = struct
            datatype binding_state
                = Unvisited of input_type option * input_expr option
                | Visiting of input_type option * input_expr option
                | Typed of output_type * input_expr option
                | Visited of output_type * output_expr option

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
        structure Id = TC.ScopeId

        datatype t = FnScope of Id.t * Name.t * Bindings.Expr.binding_state
                   | ForAllScope of Id.t * TC.Output.Type.def
                   | ExistsScope of Id.t * Bindings.Type.bindings
                   | BlockScope of Id.t * Bindings.Expr.bindings
                   | InterfaceScope of Id.t * Bindings.Expr.bindings

        val id = fn FnScope (id, _, _) => id
                  | ForAllScope (id, _) => id
                  | ExistsScope (id, _) => id
                  | BlockScope (id, _) => id
                  | InterfaceScope (id, _) => id

        fun findType scope id =
            case scope
            of ForAllScope (_, {var, kind}) => if var = id then SOME kind else NONE
             | ExistsScope (_, bindings) => Bindings.Type.find bindings id
             | FnScope _ | BlockScope _ | InterfaceScope _ => NONE

        fun findExpr scope name =
            case scope
            of FnScope (_, var, bs) => if var = name then SOME bs else NONE
             | ForAllScope _ | ExistsScope _ => NONE
             | BlockScope (_, bindings) | InterfaceScope (_, bindings) => Bindings.Expr.find bindings name
    end

    type t = Scope.t list

    val empty = []

    fun pushScope env scope = scope :: env

    fun findType env id =
        let val rec find =
                fn scope :: env =>
                    Scope.findType scope id |> Option.orElse (fn () => find env)
                 | [] => NONE
        in find env
        end

    fun freshAbstract env b =
        let val rec fresh =
                fn Scope.ExistsScope (_, bs) :: _ => Bindings.Type.fresh bs b
                 | _ :: env => fresh env
                 | [] => raise Fail "unreachable"
        in fresh env
        end

    fun newUv env pn =
        case env
        of scope :: _ => TypeVars.newUv (Scope.id scope) pn
         | [] => raise Fail "unreachable"

    fun freshUv env predicativity =
        case env
        of scope :: _ => TypeVars.freshUv (Scope.id scope) predicativity
         | [] => raise Fail "unreachable"

    fun uvInScope (env, uv) =
        List.exists (fn scope => TypeVars.uvInScope Scope.Id.compare (Scope.id scope, uv)) env

    fun findExprClosure env name =
        let val rec find =
                fn env as scope :: env' =>
                    (case Scope.findExpr scope name
                     of SOME b => SOME (b, env)
                      | NONE => find env')
                 | [] => NONE
        in find env
        end

    fun findExpr env name = Option.map #1 (findExprClosure env name)

    fun updateExpr pos env name f =
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
        in update env
        end
end

