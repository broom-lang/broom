signature TYPECHECKER_TERM = sig
    type ('typ, 'expr) expr

    val exprPos: ('typ, 'expr) expr -> Pos.t
    val exprToString: ('typ -> string) -> ('expr -> string) -> ('typ, 'expr) expr -> string
end

signature TYPECHECKER_INPUT = sig
    structure Type: sig
        type ('typ, 'expr) typ

        val pos: ('expr -> Pos.t) -> ('typ, 'expr) typ -> Pos.t
        val toString: ('typ -> string) -> ('expr -> string) -> ('typ, 'expr) typ -> string
        val shallowFoldl: ('typ * 'a -> 'a) -> 'a -> ('typ, 'expr) typ -> 'a
        val rowExtTail: {tail: 'typ -> 'typ, wrap: ('typ, 'expr) typ -> 'typ}
                      -> ('typ, 'expr) typ -> 'typ
    end

    structure Term: TYPECHECKER_TERM
end

signature TYPECHECKER_OUTPUT = sig
    structure Type: sig
        type kind
        type 'typ typ

        val kindToString: kind -> string

        val pos: 'typ typ -> Pos.t
        val toString: ('typ -> string) -> 'typ typ -> string
        val shallowFoldl: ('typ * 'a -> 'a) -> 'a -> 'typ typ -> 'a
        val rowExtTail: {tail: 'typ -> 'typ, wrap: 'typ typ -> 'typ} -> 'typ typ -> 'typ
    end

    structure Term: TYPECHECKER_TERM
end

functor Typechecking(Puts: sig
    structure Input: TYPECHECKER_INPUT
    structure Output: TYPECHECKER_OUTPUT
end) = struct
    structure Input = Puts.Input
    structure Output = Puts.Output

    datatype shade = White | Grey | Black

    type 'b binding = { shade: shade ref
                      , binder: 'b }

    type 'b bindings = 'b binding NameHashTable.hash_table

    type 'typ type_binding = { kind: Output.Type.kind
		             , typ: 'typ option }

    type ('typ, 'expr) val_binding = { typ: 'typ
                                     , value: 'expr option }

    datatype typ = InputType of (typ ref, expr ref) Input.Type.typ
                 | OutputType of typ ref Output.Type.typ
                 | ScopeType of type_scope
                 | OVar of Pos.t * ov
                 | UVar of Pos.t * uv
    
    and expr = InputExpr of (typ ref, expr ref) Input.Term.expr
             | OutputExpr of (typ ref, expr ref) Output.Term.expr
             | ScopeExpr of expr_scope

    and scope = TypeScope of type_scope
              | ExprScope of expr_scope

    withtype ov = scope TypeVars.ov
    and uv = (scope, typ) TypeVars.uv

    and type_scope = { parent: scope option ref
                     , typ: typ ref
                     , types: typ ref type_binding bindings }

    and expr_scope = { parent: scope option ref
                     , expr: expr ref
                     , vals: (typ option ref, expr ref) val_binding bindings }
    val rec exprPos =
        fn InputExpr expr => Input.Term.exprPos expr
         | OutputExpr expr => Output.Term.exprPos expr
         | ScopeExpr {expr, ...} => exprPos (!expr)

    val rec typeToString =
        fn InputType typ => Input.Type.toString (typeToString o op!) (exprToString o op!) typ
         | OutputType typ => Output.Type.toString (typeToString o op!) typ
         | ScopeType {typ, ...} => typeToString (!typ)
         | OVar (_, ov) => Name.toString (TypeVars.ovName ov)
         | UVar (_, uv) => (case TypeVars.uvGet uv
                            of Either.Right t => typeToString t
                             | Either.Left uv => Name.toString (TypeVars.uvName uv))

    and exprToString =
        fn InputExpr expr => Input.Term.exprToString (typeToString o op!) (exprToString o op!) expr
         | OutputExpr expr => Output.Term.exprToString (typeToString o op!) (exprToString o op!) expr
         | ScopeExpr {expr, ...} => exprToString (!expr)

    fun occurs uv =
        let fun occStep (t, acc) = acc orelse occ (!t)
            and occ typ =
                case typ
                of InputType t => Input.Type.shallowFoldl occStep false t
                 | OutputType t => Output.Type.shallowFoldl occStep false t
                 | ScopeType {typ, ...} => occ (!typ)
                 | OVar _ => false
                 | UVar (_, uv') => TypeVars.uvEq (uv, uv')
        in occ
        end

    structure Type = struct
        val rec pos = fn InputType typ => Input.Type.pos (exprPos o op!) typ
                       | ScopeType {typ, ...} => pos (!typ)
                       | OutputType typ => Output.Type.pos typ

        val rec rowExtTail =
            fn OutputType t => Output.Type.rowExtTail {tail = rowExtTail o op!, wrap = ref o OutputType} t
             | InputType t => Input.Type.rowExtTail {tail = rowExtTail o op!, wrap = ref o InputType} t
             | ScopeType {typ, ...} => rowExtTail (!typ)
             | t as OVar _ | t as UVar _ => ref t
    end

    structure Scope = struct
        val parent =
            fn TypeScope {parent, ...} => !parent
             | ExprScope {parent, ...} => !parent

        fun valBindingToString name {binder = {typ, value}, shade = _} =
            let val typeStr = case !typ
                              of SOME typ => " : " ^ typeToString typ
                               | NONE => ""
                val valueStr = case value
                               of SOME (ref expr) => " = " ^ exprToString expr
                                | NONE => ""
            in Name.toString name ^ typeStr ^ valueStr
            end

        fun typeBindingToString name {binder = {kind, typ}, shade = _} =
            let val typeStr = case typ
                              of SOME (ref typ) => " = " ^ typeToString typ
                               | NONE => ""
            in Name.toString name ^ " : " ^ Output.Type.kindToString kind ^ typeStr
            end

        fun bindingsToString bindingToString bindings =
            NameHashTable.foldi (fn (name, binding, acc) =>
                                     acc ^ bindingToString name binding ^ "\n")
                                "" bindings

        val valsToString = bindingsToString valBindingToString

        val typesToString = bindingsToString typeBindingToString

        val rec toString =
            fn ExprScope {parent, vals, expr = _} =>
                let val parentStr = case !parent
                                    of SOME parent => toString parent
                                     | NONE => ""
                in parentStr ^ valsToString vals
                end
             | TypeScope {parent, types, typ = _} =>
                let val parentStr = case !parent
                                    of SOME parent => toString parent
                in parentStr ^ typesToString types
                end

        val eq = fn (TypeScope {types, ...}, TypeScope {types = types', ...}) => MLton.eq (types, types')
                  | (ExprScope {vals, ...}, ExprScope {vals = vals', ...}) => MLton.eq (vals, vals')
                  | _ => false

        fun compare (scope, scope') =
            let fun indexOf ancestor scope =
                    let fun loop i scope =
                           if eq (scope, ancestor)
                           then SOME i
                           else Option.mapPartial (loop (i + 1)) (parent scope)
                    in loop 0 scope
                    end
            in case indexOf scope' scope
               of SOME i => if i > 0 then LESS else EQUAL
                | NONE => (case indexOf scope scope'
                           of SOME i => if i > 0 then GREATER else EQUAL
                            | NONE => raise Fail "incomparable scopes")
            end
    end

    val ovEq: scope TypeVars.ov * ov -> bool = TypeVars.ovEq Scope.eq
    val ovInScope: scope * ov -> bool = TypeVars.ovInScope Scope.compare
    val uvMerge: uv * uv -> unit = TypeVars.uvMerge Scope.compare
    val uvInScope: scope * uv -> bool = TypeVars.uvInScope Scope.compare
end

structure TypecheckingCst = Typechecking(struct
    structure Input = Cst
    structure Output = FAst
end)

