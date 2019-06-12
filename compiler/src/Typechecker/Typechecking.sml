signature TYPECHECKER_INPUT = sig
    structure Type: sig
        type ('typ, 'expr) typ

        val pos: ('expr -> Pos.t) -> ('typ, 'expr) typ -> Pos.t
        val toDoc: ('typ -> PPrint.t) -> ('expr -> PPrint.t) -> ('typ, 'expr) typ -> PPrint.t
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
        type def = {var: Name.t, kind: kind}
        type 'sv concr
        type 'sv abs

        val kindToDoc: kind -> PPrint.t

        val splitExistentials: 'typ abs -> def list * 'typ concr 
        val rowExtTail: 'typ concr -> 'typ concr

        structure Concr: sig
            val pos: 'sv concr -> Pos.t
            val toDoc: ('sv -> PPrint.t) -> 'sv concr -> PPrint.t
            val occurs: ('uv -> 'sv -> bool) -> 'uv -> 'sv concr -> bool
            val substitute: (Name.t * 'sv concr -> 'sv -> 'sv concr option) 
                          -> Name.t * 'sv concr -> 'sv concr -> 'sv concr
        end

        structure Abs: sig
            val pos: 'sv abs -> Pos.t
            val toDoc: ('sv -> PPrint.t) -> 'sv abs -> PPrint.t
            val occurs: ('uv -> 'sv -> bool) -> 'uv -> 'sv abs -> bool
            val substitute: (Name.t * 'sv concr -> 'sv -> 'sv concr option) 
                          -> Name.t * 'sv concr -> 'sv abs -> 'sv abs
        end
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

    type 'typ type_binder = {kind: Output.Type.kind, typ: 'typ}

    type ('typ, 'expr) val_binder = {typ: 'typ, value: 'expr option}

    type 'binder bindings = 'binder binding NameHashTable.hash_table (* HACK: should be opaque *)

    type scope_id

    datatype typ = InputType of (typ, expr) Input.Type.typ
                 | OutputType of sv Output.Type.concr
                 | ScopeType of {scope: type_scope, typ: typ}
    
    and sv = OVar of Pos.t * ov
           | UVar of Pos.t * uv
    
    and expr = InputExpr of (typ, typ option ref, expr, expr ref) Input.Term.expr
             | OutputExpr of typ Output.Term.expr
             | ScopeExpr of {scope: expr_scope, expr: expr}

    and scope = TypeScope of type_scope
              | ExprScope of expr_scope

    and type_scope = TFnScope of scope_id * Name.t * type_binding option ref
                   | InterfaceScope of scope_id * type_bindings

    and expr_scope = FnScope of scope_id * Name.t * expr_binding
                   | BlockScope of scope_id * expr_bindings

    withtype ov = scope list TypeVars.ov
    and uv = (scope list, sv Output.Type.concr) TypeVars.uv

    and type_binding = typ ref type_binder binding
    and type_bindings = typ ref type_binder bindings
    and expr_binding = (typ option ref, expr ref) val_binder binding
    and expr_bindings = (typ option ref, expr ref) val_binder bindings

    and env = scope list

    structure Type: sig
        val pos: typ -> Pos.t
        val toDoc: typ -> PPrint.t
        val toString: typ -> string
        val substitute: Name.t * sv Output.Type.concr -> sv Output.Type.concr -> sv Output.Type.concr
    end

    structure Expr: sig
        val pos: expr -> Pos.t
        val toDoc: expr -> PPrint.t
        val toString: expr -> string
    end

    structure Scope: sig
        val forFn: Name.t * expr_binding -> expr_scope
        val forBlock: expr_bindings -> expr_scope
        val forTFn: Name.t * type_binding option ref -> type_scope
        
        val exprFind: expr_scope -> Name.t -> expr_binding option
        val typeFind: type_scope -> Name.t -> type_binding option
    end

    structure Env: sig
        type env = env
        
        val pushExprScope: env -> expr_scope -> env
        val parent: env -> env option
        val exprFind: env -> Name.t -> expr_binding option
        val typeFind: env -> Name.t -> type_binding option
    end

    val concrOccurs: uv -> sv Output.Type.concr -> bool
    val ovEq: ov * ov -> bool
    val ovInScope: env * ov -> bool
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
    type 'typ Output.Type.concr = 'typ Puts.Output.Type.concr and
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

    type 'typ type_binder = {kind: Output.Type.kind, typ: 'typ}

    type ('typ, 'expr) val_binder = {typ: 'typ, value: 'expr option}

    type scope_id = int

    datatype typ = InputType of (typ, expr) Input.Type.typ
                 | OutputType of sv Output.Type.concr
                 | ScopeType of {scope: type_scope, typ: typ}

    and sv = OVar of Pos.t * ov
           | UVar of Pos.t * uv
    
    and expr = InputExpr of (typ, typ option ref, expr, expr ref) Input.Term.expr
             | OutputExpr of typ Output.Term.expr
             | ScopeExpr of {scope: expr_scope, expr: expr}

    and scope = TypeScope of type_scope
              | ExprScope of expr_scope

    and type_scope = TFnScope of scope_id * Name.t * type_binding option ref
                   | InterfaceScope of scope_id * type_bindings

    and expr_scope = FnScope of scope_id * Name.t * expr_binding
                   | BlockScope of scope_id * expr_bindings

    withtype ov = scope list TypeVars.ov
    and uv = (scope list, sv Output.Type.concr) TypeVars.uv

    and type_binding = typ ref type_binder binding
    and type_bindings = typ ref type_binder bindings
    and expr_binding = (typ option ref, expr ref) val_binder binding
    and expr_bindings = (typ option ref, expr ref) val_binder bindings

    and env = scope list

    val rec typeToDoc =
        fn InputType typ => Input.Type.toDoc typeToDoc exprToDoc typ
         | OutputType typ => Output.Type.Concr.toDoc svarToDoc typ
         | ScopeType {typ, ...} => typeToDoc typ
 
    and svarToDoc =
        fn OVar (_, ov) => Name.toDoc (TypeVars.ovName ov)
         | UVar (_, uv) => (case TypeVars.uvGet uv
                            of Either.Right t => Output.Type.Concr.toDoc svarToDoc t
                             | Either.Left uv => text "^" <> Name.toDoc (TypeVars.uvName uv))
   
    and annToDoc = fn ann => Option.mapOr (fn t => text ":" <+> typeToDoc t) PPrint.empty (!ann)

    and exprToDoc =
        fn InputExpr expr => Input.Term.exprToDoc typeToDoc annToDoc exprToDoc (exprToDoc o op!) expr
         | OutputExpr expr => Output.Term.exprToDoc typeToDoc expr
         | ScopeExpr {expr, ...} => exprToDoc expr

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
                       | OutputType typ => Output.Type.Concr.pos typ

        val toDoc = typeToDoc
        val toString = PPrint.pretty 80 o toDoc

        fun substitute kv = Output.Type.Concr.substitute svarSubstitute kv

        and svarSubstitute (kv as (name, t')) =
            fn OVar (_, ov) => (* TODO: Check first whether `ov` is in scope and return NONE if it is: *)
                if TypeVars.ovName ov = name then SOME t' else NONE (* HACK? *)
             | UVar (_, uv) => (case TypeVars.uvGet uv
                                of Either.Left _ => NONE
                                 | Either.Right t => SOME (substitute kv t))
    end

    structure Scope = struct
        local val counter = ref 0
        in fun allocId () = let val id = !counter
                            in counter := id + 1
                             ; id
                            end
        end

        fun forFn (name, binding) = FnScope (allocId (), name, binding)
        fun forBlock vals = BlockScope (allocId (), vals)
        fun forTFn (name, binding) = TFnScope (allocId (), name, binding)

        fun id ( TypeScope (TFnScope (id, _, _) | InterfaceScope (id, _))
               | ExprScope (FnScope (id, _, _) | BlockScope (id, _)) ) = id

        fun exprFind scope name =
            case scope
            of FnScope (_, name', binding) => if name' = name then SOME binding else NONE
             | BlockScope (_, bindings) => NameHashTable.find bindings name

        fun typeFind scope name =
            case scope
            of TFnScope (_, name', binding) =>
                if name' = name
                then case !binding
                     of SOME binding => SOME binding
                      | NONE => raise Fail ("uninitialized binding for " ^ Name.toString name)
                else NONE
             | InterfaceScope (_, bindings) => NameHashTable.find bindings name

        val eq = op= o Pair.bimap id id

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
            let val typeDoc = text " =" <+> typeToDoc (!typ)
            in Name.toDoc name <+> text ":" <+> Output.Type.kindToDoc kind <> typeDoc
            end

        fun bindingsToDoc bindingToDoc bindings =
            NameHashTable.foldi (fn (name, binding, acc) =>
                                     acc <> bindingToDoc name binding <> PPrint.newline)
                                PPrint.empty bindings

        val valsToDoc = bindingsToDoc valBindingToDoc

        val typesToDoc = bindingsToDoc typeBindingToDoc

        val rec toDoc =
            fn ExprScope (FnScope (_, name, binding)) => valBindingToDoc name binding
             | ExprScope (BlockScope (_, vals)) => valsToDoc vals
             | TypeScope (TFnScope (_, name, ref (SOME binding))) => typeBindingToDoc name binding
             | TypeScope (InterfaceScope (_, types)) => typesToDoc types
    end

    structure Env = struct
        type env = env

        fun pushExprScope env scope = ExprScope scope :: env

        val parent = fn [] => NONE
                      | _ :: env' => SOME env'

        fun exprFind env name =
            case env
            of ExprScope scope :: env => (case Scope.exprFind scope name
                                          of SOME binding => SOME binding
                                           | NONE => exprFind env name)
             | TypeScope _ :: env => exprFind env name
             | [] => NONE

        fun typeFind env name =
            case env
            of TypeScope scope :: env => (case Scope.typeFind scope name
                                          of SOME binding => SOME binding
                                           | NONE => typeFind env name)
             | ExprScope _ :: env => typeFind env name
             | [] => NONE

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

        (* OPTIMIZE: *)
        fun eq envs = case compare envs
                      of EQUAL => true
                       | _ => false
    end

    fun concrOccurs uv = Output.Type.Concr.occurs svarOccurs uv
    and svarOccurs uv =
        fn OVar _ => false
         | UVar (_, uv) => (case TypeVars.uvGet uv
                            of Either.Left uv' => TypeVars.uvEq (uv', uv)
                             | Either.Right t => concrOccurs uv t)

    val ovEq = TypeVars.ovEq Env.eq
    val ovInScope = TypeVars.ovInScope Env.compare
    val uvMerge: uv * uv -> unit = TypeVars.uvMerge Env.compare
    val uvInScope: env * uv -> bool = TypeVars.uvInScope Env.compare
end

structure TypecheckingCst = Typechecking(struct
    structure Input = Cst
    structure Output = FAst
end)

