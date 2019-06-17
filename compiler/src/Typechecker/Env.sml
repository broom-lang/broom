structure TypecheckingEnv :> sig
    structure TC: TYPECHECKING

    type input_type = (TC.typ, TC.typ option ref, TC.expr) TC.Input.Type.typ
    type input_expr = (TC.typ, TC.typ option ref, TC.expr, TC.expr ref) TC.Input.Term.expr
    type output_type = TC.sv TC.Output.Type.concr
    type output_expr = TC.sv TC.Output.Term.expr

    structure Bindings: sig
        structure Type: sig
            type binding = TC.Output.Type.kind
            type bindings

            val new: unit -> bindings
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
        datatype t = FnScope of Name.t * Bindings.Expr.binding_state
                   | ForAllScope of TC.Output.Type.def
                   | ExistsScope of Bindings.Type.bindings
                   | BlockScope of Bindings.Expr.bindings
                   | InterfaceScope of Bindings.Expr.bindings
    end

    type t

    val empty: t
    val pushScope: t -> Scope.t -> t
    val findType: t -> Id.t -> Bindings.Type.binding option
    val freshAbstract: t -> Bindings.Type.binding -> Id.t
    val findExpr: t -> Name.t -> Bindings.Expr.binding_state option
    val updateExpr: Pos.t -> t -> Name.t
                  -> (Bindings.Expr.binding_state -> Bindings.Expr.binding_state) -> unit
end = struct
    open TypeError
    structure TC = TypecheckingCst

    type input_type = (TC.typ, TC.typ option ref, TC.expr) TC.Input.Type.typ
    type input_expr = (TC.typ, TC.typ option ref, TC.expr, TC.expr ref) TC.Input.Term.expr
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
        datatype t = FnScope of Name.t * Bindings.Expr.binding_state
                   | ForAllScope of TC.Output.Type.def
                   | ExistsScope of Bindings.Type.bindings
                   | BlockScope of Bindings.Expr.bindings
                   | InterfaceScope of Bindings.Expr.bindings

        fun findType scope id =
            case scope
            of ForAllScope {var, kind} => if var = id then SOME kind else NONE
             | ExistsScope bindings => Bindings.Type.find bindings id
             | FnScope _ | BlockScope _ | InterfaceScope _ => NONE

        fun findExpr scope name =
            case scope
            of FnScope (var, bs) => if var = name then SOME bs else NONE
             | ForAllScope _ | ExistsScope _ => NONE
             | BlockScope bindings | InterfaceScope bindings => Bindings.Expr.find bindings name
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
                fn Scope.ExistsScope bs :: _ => Bindings.Type.fresh bs b
                 | _ :: env => fresh env
                 | [] => raise Fail "unreachable"
        in fresh env
        end

    fun findExpr env name =
        let val rec find =
                fn scope :: env =>
                    Scope.findExpr scope name |> Option.orElse (fn () => find env)
                 | [] => NONE
        in find env
        end

    fun updateExpr pos env name f =
        let val rec update =
                fn (Scope.BlockScope bs | Scope.InterfaceScope bs) :: env =>
                    (case Bindings.Expr.find bs name
                     of SOME v => NameHashTable.insert bs (name, f v)
                      | NONE => update env)
                 | Scope.FnScope (var, _) :: env =>
                    if var = name
                    then raise Fail "unreachable"
                    else update env
                 | (Scope.ForAllScope _ | Scope.ExistsScope _) :: env => update env
                 | [] =>  raise TypeError (UnboundVal (pos, name))
        in update env
        end
end

