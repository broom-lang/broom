signature TYPECHECKER_OUTPUT = sig
    structure Type: sig
        type kind
        type 'typ typ

        val pos: 'typ typ -> Pos.t
        val toString: ('typ -> string) -> 'typ typ -> string
        val shallowFoldl: ('typ * 'a -> 'a) -> 'a -> 'typ typ -> 'a
    end

    structure Term: sig
        type ('typ, 'expr) expr

        val exprPos: ('typ, 'expr) expr -> Pos.t
        val exprToString: ('typ -> string) -> ('expr -> string) -> ('typ, 'expr) expr -> string
    end
end

signature TYPECHECKER_INPUT = sig
    include TYPECHECKER_OUTPUT
    
    structure Interface: sig
        type ('itf, 'typ) interface
    end
    
    structure Module: sig
       type ('itf, 'mod, 'typ, 'expr) mod
    end
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

    type 'typ type_binding = { kind: Input.Type.kind
		             , typ: 'typ option }

    type ('typ, 'expr) val_binding = { typ: 'typ
                                     , value: 'expr option }

    datatype typ = InputType of typ ref Input.Type.typ
                 | OutputType of typ ref Output.Type.typ
                 | ScopeType of type_scope
                 | OVar of ov
                 | UVar of uv
    
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

    val rec typeToString =
        fn InputType typ => Input.Type.toString (typeToString o op!) typ
         | OutputType typ => Output.Type.toString (typeToString o op!) typ
         | ScopeType {typ, ...} => typeToString (!typ)
         | OVar ov => Name.toString (TypeVars.ovName ov)
         | UVar uv => Name.toString (TypeVars.uvName uv)

    val rec exprPos =
        fn InputExpr expr => Input.Term.exprPos expr
         | OutputExpr expr => Output.Term.exprPos expr
         | ScopeExpr {expr, ...} => exprPos (!expr)

    val rec exprToString =
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
                 | UVar uv' => TypeVars.uvEq (uv, uv')
        in occ
        end

    val scopeParent =
        fn TypeScope {parent, ...} => !parent
         | ExprScope {parent, ...} => !parent

    val scopeEq = MLton.eq

    fun compareScopes (scope, scope') =
        let fun indexOf ancestor scope =
                let fun loop i scope =
                       if scopeEq (scope, ancestor)
                       then SOME i
                       else Option.mapPartial (loop (i + 1)) (scopeParent scope)
                in loop 0 scope
                end
        in case indexOf scope' scope
           of SOME i => if i > 0 then LESS else EQUAL
            | NONE => (case indexOf scope scope'
                       of SOME i => if i > 0 then GREATER else EQUAL
                        | NONE => raise Fail "incomparable scopes")
        end

    val ovEq: scope TypeVars.ov * ov -> bool = TypeVars.ovEq scopeEq
    val ovInScope: scope * ov -> bool = TypeVars.ovInScope compareScopes
    val uvMerge: uv * uv -> unit = TypeVars.uvMerge compareScopes
    val uvInScope: scope * uv -> bool = TypeVars.uvInScope compareScopes

    structure Type = struct
        val rec pos = fn InputType typ => Input.Type.pos typ
                       | ScopeType {typ, ...} => pos (!typ)
                       | OutputType typ => Output.Type.pos typ
    end
end

structure TypecheckingCst = Typechecking(struct
    structure Input = Cst
    structure Output = FAst
end)

