signature TYPECHECKER_INPUT = sig
    structure Type: sig
        type ('typ, 'expr) typ

        val pos: ('expr -> Pos.t) -> ('typ, 'expr) typ -> Pos.t
        val toDoc: ('typ -> PPrint.t) -> ('expr -> PPrint.t) -> ('typ, 'expr) typ -> PPrint.t
        val shallowFoldl: ('typ * 'a -> 'a) -> 'a -> ('typ, 'expr) typ -> 'a
        val rowExtTail: ('typ, 'expr) typ -> ('typ, 'expr) typ
    end

    structure Term: sig
        type ('typ, 'bt, 'expr, 'be) expr

        val exprPos: ('typ, 'bt, 'expr, 'be) expr -> Pos.t
        val exprToDoc: ('typ -> PPrint.t) -> ('bt -> PPrint.t) -> ('expr -> PPrint.t) -> ('be -> PPrint.t)
                        -> ('typ, 'bt, 'expr, 'be) expr -> PPrint.t
    end
end

signature TYPECHECKER_OUTPUT = sig
    structure Type: sig
        type kind
        type 'typ typ

        val kindToDoc: kind -> PPrint.t

        val pos: 'typ typ -> Pos.t
        val toDoc: ('typ -> PPrint.t) -> 'typ typ -> PPrint.t
        val shallowFoldl: ('typ * 'a -> 'a) -> 'a -> 'typ typ -> 'a
        val substitute: ('typ typ -> 'typ) -> (Name.t * 'typ -> 'typ -> 'typ)
                        -> Name.t * 'typ -> 'typ typ -> 'typ
        val rowExtTail: {tail: 'typ -> 'typ, wrap: 'typ typ -> 'typ} -> 'typ typ -> 'typ
    end

    structure Term: sig
        type 'typ expr

        val exprPos: 'typ expr -> Pos.t
        val exprToDoc: ('typ -> PPrint.t) -> 'typ expr -> PPrint.t
    end
end

signature TYPECHECKING = sig
    structure Input: TYPECHECKER_INPUT
    structure Output: TYPECHECKER_OUTPUT

    datatype shade = White | Grey | Black
    
    type 'b binding = { shade: shade ref
                      , binder: 'b }

    type 'typ type_binding = { kind: Output.Type.kind
		             , typ: 'typ option }

    type 'binder bindings = 'binder binding NameHashTable.hash_table (* HACK: should be opaque *)

    type ('typ, 'expr) val_binding = { typ: 'typ
                                     , value: 'expr option }

    type scope_id

    datatype typ = InputType of (typ, expr) Input.Type.typ
                 | OutputType of typ Output.Type.typ
                 | ScopeType of {scope: type_scope, typ: typ}
                 | OVar of Pos.t * ov
                 | UVar of Pos.t * uv
    
    and expr = InputExpr of (typ, typ option ref, expr, expr ref) Input.Term.expr
             | OutputExpr of typ Output.Term.expr
             | ScopeExpr of {scope: expr_scope, expr: expr}

    and scope = TypeScope of type_scope
              | ExprScope of expr_scope

    and type_scope = TFnScope of scope_id * type_bindings
                   | InterfaceScope of scope_id * type_bindings

    and expr_scope = FnScope of scope_id * expr_bindings
                   | BlockScope of scope_id * expr_bindings

    withtype ov = scope list TypeVars.ov
    and uv = (scope list, typ) TypeVars.uv

    and type_bindings = typ ref type_binding bindings
    and expr_bindings = (typ option ref, expr ref) val_binding bindings

    and env = scope list

    structure Type: sig
        val pos: typ -> Pos.t
        val toDoc: typ -> PPrint.t
        val toString: typ -> string
        val substitute: Name.t * typ -> typ -> typ
        val rowExtTail: typ -> typ
    end

    structure Expr: sig
        val pos: expr -> Pos.t
        val toDoc: expr -> PPrint.t
        val toString: expr -> string
    end

    structure Scope: sig
        val forFn: expr_bindings -> expr_scope
        val forBlock: expr_bindings -> expr_scope
    end

    structure Env: sig
        type env = env
        
        val pushExprScope: env -> expr_scope -> env
        val parent: env -> env option
    end

    val occurs: uv -> typ -> bool
    val uvInScope: env * uv -> bool
    val uvMerge: uv * uv -> unit
end

functor Typechecking(Puts: sig
    structure Input: TYPECHECKER_INPUT
    structure Output: TYPECHECKER_OUTPUT
end) :> TYPECHECKING where
    type ('typ, 'expr) Input.Type.typ = ('typ, 'expr) Puts.Input.Type.typ and
    type ('typ, 'bt, 'expr, 'be) Input.Term.expr = ('typ, 'bt, 'expr, 'be) Puts.Input.Term.expr and
    type Output.Type.kind = Puts.Output.Type.kind and
    type 'typ Output.Type.typ = 'typ Puts.Output.Type.typ and
    type 'typ Output.Term.expr = 'typ Puts.Output.Term.expr
= struct
    structure Input = Puts.Input
    structure Output = Puts.Output

    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    datatype shade = White | Grey | Black

    type 'b binding = { shade: shade ref
                      , binder: 'b }

    type 'b bindings = 'b binding NameHashTable.hash_table

    type 'typ type_binding = { kind: Output.Type.kind
		             , typ: 'typ option }

    type ('typ, 'expr) val_binding = { typ: 'typ
                                     , value: 'expr option }

    type scope_id = int

    datatype typ = InputType of (typ, expr) Input.Type.typ
                 | OutputType of typ Output.Type.typ
                 | ScopeType of {scope: type_scope, typ: typ}
                 | OVar of Pos.t * ov
                 | UVar of Pos.t * uv
    
    and expr = InputExpr of (typ, typ option ref, expr, expr ref) Input.Term.expr
             | OutputExpr of typ Output.Term.expr
             | ScopeExpr of {scope: expr_scope, expr: expr}

    and scope = TypeScope of type_scope
              | ExprScope of expr_scope

    and type_scope = TFnScope of scope_id * type_bindings
                   | InterfaceScope of scope_id * type_bindings

    and expr_scope = FnScope of scope_id * expr_bindings
                   | BlockScope of scope_id * expr_bindings

    withtype ov = scope list TypeVars.ov
    and uv = (scope list, typ) TypeVars.uv

    and type_bindings = typ ref type_binding bindings
    and expr_bindings = (typ option ref, expr ref) val_binding bindings

    and env = scope list

    val rec typeToDoc =
        fn InputType typ => Input.Type.toDoc typeToDoc exprToDoc typ
         | OutputType typ => Output.Type.toDoc typeToDoc typ
         | ScopeType {typ, ...} => typeToDoc typ
         | OVar (_, ov) => Name.toDoc (TypeVars.ovName ov)
         | UVar (_, uv) => (case TypeVars.uvGet uv
                            of Either.Right t => typeToDoc t
                             | Either.Left uv => Name.toDoc (TypeVars.uvName uv))

    and annToDoc = fn ann => Option.mapOr (fn t => text ":" <+> typeToDoc t) PPrint.empty (!ann)

    and exprToDoc =
        fn InputExpr expr => Input.Term.exprToDoc typeToDoc annToDoc exprToDoc (exprToDoc o op!) expr
         | OutputExpr expr => Output.Term.exprToDoc typeToDoc expr
         | ScopeExpr {expr, ...} => exprToDoc expr

    fun occurs uv =
        let fun occStep (t, acc) = acc orelse occ t
            and occ typ =
                case typ
                of InputType t => raise Fail "unreachable"
                 | OutputType t => Output.Type.shallowFoldl occStep false t
                 | ScopeType {typ, ...} => occ typ
                 | OVar _ => false
                 | UVar (_, uv') => TypeVars.uvEq (uv, uv')
        in occ
        end

    structure Expr = struct
        val rec pos =
            fn InputExpr expr => Input.Term.exprPos expr
             | OutputExpr expr => Output.Term.exprPos expr
             | ScopeExpr {expr, ...} => pos expr

        val toDoc = exprToDoc
        val toString = PPrint.pretty 80 o toDoc
    end

    structure Type = struct
        val rec pos = fn InputType typ => Input.Type.pos Expr.pos typ
                       | ScopeType {typ, ...} => pos typ
                       | OutputType typ => Output.Type.pos typ

        val toDoc = typeToDoc
        val toString = PPrint.pretty 80 o toDoc

        fun substitute (kv: Name.t * typ) =
            fn OutputType t => Output.Type.substitute OutputType substitute kv t
             | InputType _ => raise Fail "encountered InputType"
             | ScopeType _ => raise Fail "encountered ScopeType"

        val rec rowExtTail =
            fn OutputType t => Output.Type.rowExtTail {tail = rowExtTail, wrap = OutputType} t
             | InputType t => InputType (Input.Type.rowExtTail t)
             | ScopeType {typ, ...} => rowExtTail typ
             | t as OVar _ | t as UVar _ => t
    end

    structure Scope = struct
        local val counter = ref 0
        in fun allocId () = let val id = !counter
                            in counter := id + 1
                             ; id
                            end
        end

        fun forFn vals = FnScope (allocId (), vals)
        fun forBlock vals = BlockScope (allocId (), vals)

        fun id ( TypeScope (TFnScope (id, _) | InterfaceScope (id, _))
               | ExprScope (FnScope (id, _) | BlockScope (id, _)) ) = id

        val eq = MLton.eq o Pair.bimap id id

        fun valBindingToDoc name {binder = {typ, value}, shade = _} =
            let val typeDoc = case !typ
                              of SOME typ => text " :" <+> typeToDoc typ
                               | NONE => PPrint.empty 
                val valueDoc = case value
                               of SOME (ref expr) => text " =" <+> exprToDoc expr
                                | NONE => PPrint.empty
            in Name.toDoc name <> typeDoc <> valueDoc
            end

        fun typeBindingToDoc name {binder = {kind, typ}, shade = _} =
            let val typeDoc = case typ
                              of SOME (ref typ) => text " =" <+> typeToDoc typ
                               | NONE => PPrint.empty
            in Name.toDoc name <+> text ":" <+> Output.Type.kindToDoc kind <> typeDoc
            end

        fun bindingsToDoc bindingToDoc bindings =
            NameHashTable.foldi (fn (name, binding, acc) =>
                                     acc <> bindingToDoc name binding <> PPrint.newline)
                                PPrint.empty bindings

        val valsToDoc = bindingsToDoc valBindingToDoc

        val typesToDoc = bindingsToDoc typeBindingToDoc

        val rec toDoc =
            fn ExprScope (FnScope (_, vals) | BlockScope (_, vals)) => valsToDoc vals
             | TypeScope (TFnScope (_, types) | InterfaceScope (_, types)) => typesToDoc types
    end

    structure Env = struct
        type env = env

        fun pushExprScope env scope = ExprScope scope :: env

        val parent = fn [] => NONE
                      | _ :: env' => SOME env'

        val toDoc = List.foldl (fn (scope, parentDoc) => Scope.toDoc scope <> parentDoc) PPrint.empty
        
        fun compare (env, env') =
            let fun indexOf env scope =
                    let fun loop i = fn scope' :: env' =>
                                         if Scope.eq (scope', scope)
                                         then SOME i
                                         else loop (i + 1) env'
                                      | [] => NONE
                    in loop 0 env
                    end
            in case env
               of scope :: _ =>
                   (case indexOf env' scope
                    of SOME i => if i > 0 then GREATER else EQUAL
                     | NONE => (case env'
                                of scope' :: _ => (case indexOf env scope'
                                                   of SOME i => if i > 0 then LESS else EQUAL
                                                    | NONE => raise Fail "incomparable scopes")
                                 | [] => LESS))
                | [] => if List.null env' then EQUAL else GREATER
            end
    end

    val uvMerge: uv * uv -> unit = TypeVars.uvMerge Env.compare
    val uvInScope: env * uv -> bool = TypeVars.uvInScope Env.compare
end

structure TypecheckingCst = Typechecking(struct
    structure Input = Cst
    structure Output = FAst
end)

