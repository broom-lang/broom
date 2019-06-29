structure TypecheckingEnv :> sig
    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type output_type = FlexFAst.Type.concr
    type output_expr = FlexFAst.Term.expr

    structure Bindings: sig
        structure Type: sig
            type binding = FlexFAst.Type.kind
            type bindings

            val new: unit -> bindings
            val fresh: bindings -> binding -> Id.t
            val defs: bindings -> FlexFAst.Type.def list
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
        structure Id: ID where type t = FlexFAst.ScopeId.t

        datatype t = FnScope of Id.t * Name.t * Bindings.Expr.binding_state
                   | ForAllScope of Id.t * FlexFAst.Type.def
                   | ExistsScope of Id.t * Bindings.Type.bindings
                   | BlockScope of Id.t * Bindings.Expr.bindings
                   | InterfaceScope of Id.t * Bindings.Expr.bindings
                   | Marker of Id.t
    end

    type t

    val empty: t
    val pushScope: t -> Scope.t -> t
    val scopeIds: t -> Scope.Id.t list
    val hasScope: t -> Scope.Id.t -> bool

    val findType: t -> Id.t -> Bindings.Type.binding option
    val bigLambdaParams: t -> FlexFAst.Type.def vector
    val newUv: t -> TypeVars.predicativity * Name.t -> FlexFAst.Type.uv
    val freshUv: t -> TypeVars.predicativity -> FlexFAst.Type.uv
    val freshAbstract: t -> int -> FlexFAst.Type.def -> Name.t
   
    val findExpr: t -> Name.t -> Bindings.Expr.binding_state option
    val findExprClosure: t -> Name.t -> (Bindings.Expr.binding_state * t) option
    val updateExpr: Pos.t -> t -> Name.t
                  -> (Bindings.Expr.binding_state -> Bindings.Expr.binding_state) -> unit
end = struct
    open TypeError
    structure FAst = FlexFAst

    type input_type = Cst.Type.typ
    type input_expr = Cst.Term.expr
    type output_type = FAst.Type.concr
    type output_expr = FAst.Term.expr

    val op|> = Fn.|>

    structure Bindings = struct
        structure Type = struct
            type binding = FAst.Type.kind
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
        structure Id = FAst.ScopeId

        datatype t = FnScope of Id.t * Name.t * Bindings.Expr.binding_state
                   | ForAllScope of Id.t * FAst.Type.def
                   | ExistsScope of Id.t * Bindings.Type.bindings
                   | BlockScope of Id.t * Bindings.Expr.bindings
                   | InterfaceScope of Id.t * Bindings.Expr.bindings
                   | Marker of Id.t

        val id = fn FnScope (id, _, _) => id
                  | ForAllScope (id, _) => id
                  | ExistsScope (id, _) => id
                  | BlockScope (id, _) => id
                  | InterfaceScope (id, _) => id
                  | Marker id => id

        fun findType scope id =
            case scope
            of ForAllScope (_, {var, kind}) => if var = id then SOME kind else NONE
             | ExistsScope (_, bindings) => Bindings.Type.find bindings id
             | FnScope _ | BlockScope _ | InterfaceScope _ | Marker _ => NONE

        fun findExpr scope name =
            case scope
            of FnScope (_, var, bs) => if var = name then SOME bs else NONE
             | ForAllScope _ | ExistsScope _ | Marker _ => NONE
             | BlockScope (_, bindings) | InterfaceScope (_, bindings) => Bindings.Expr.find bindings name
    end

    type t = {scopeIds: Scope.Id.t list, scopes: Scope.t list}

    val empty = {scopeIds = [], scopes = []}

    fun pushScope {scopeIds, scopes} scope =
        {scopes = scope :: scopes, scopeIds = Scope.id scope :: scopeIds}

    fun scopeIds {scopeIds, scopes = _} = scopeIds

    fun hasScope (env: t) id =
        List.exists (fn id' => id' = id) (#scopeIds env)

    fun findType (env: t) id =
        let val rec find =
                fn scope :: env =>
                    Scope.findType scope id |> Option.orElse (fn () => find env)
                 | [] => NONE
        in find (#scopes env)
        end

    fun bigLambdaParams env = #[] (* FIXME *)

    fun newUv (env: t) (predicativity, name) =
        case #scopes env
        of scope :: _ => TypeVars.Uv.new (Scope.id scope, predicativity, name)
         | [] => raise Fail "unreachable"

    fun freshUv (env: t) predicativity =
        case #scopes env
        of scope :: _ => TypeVars.Uv.fresh (Scope.id scope, predicativity)
         | [] => raise Fail "unreachable"

    fun freshAbstract env arity {var, kind} =
        (* FIXME: Put into toplevel so that we can emit it. *)
        ("g__" ^ Id.toString var) |> Name.fromString |> Name.freshen

    fun findExprClosure (env: t) name =
        let val rec find =
                fn env as {scopes = scope :: scopes, scopeIds = _ :: scopeIds} =>
                    (case Scope.findExpr scope name
                     of SOME b => SOME (b, env)
                      | NONE => find {scopes, scopeIds})
                 | {scopes = [], scopeIds = []} => NONE
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
end

