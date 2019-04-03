signature TYPECHECKER_OUTPUT = sig
    structure Type: sig
        type kind
        type 'typ typ
    end

    structure Term: sig
        type ('typ, 'expr) expr
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

    type 'itf itf_binding = { interface: 'itf 
                            , shade: shade }

    type ('itf, 'mod) mod_binding = { interface: 'itf
                                    , mod: 'mod option }

    datatype typ = InputType of typ ref Input.Type.typ
                 | OutputType of typ ref Output.Type.typ
                 | ScopeType of type_scope
    
    and expr = InputExpr of (typ ref, expr ref) Input.Term.expr
             | OutputExpr of (typ ref, expr ref) Output.Term.expr
             | ScopeExpr of expr_scope

    and interface = InputItf of (interface ref, typ ref) Input.Interface.interface
                  | OutputItf of typ ref Output.Type.typ
                  | ScopeItf of interface_scope

    and mod = InputMod of (interface ref, mod ref, typ ref, expr ref) Input.Module.mod
            | OutputMod of (typ ref, expr ref) Output.Term.expr
            | ScopeMod of mod_scope

    and scope = ItfScope of interface_scope
              | ModScope of mod_scope
              | TypeScope of type_scope
              | ExprScope of expr_scope

    withtype mod_scope = { parent: scope option ref
                         , mod: mod ref
                         , interfaces: interface ref itf_binding bindings
                         , mods: (interface ref, mod ref) mod_binding bindings
                         , types: typ ref type_binding bindings
                         , vals: (typ ref, expr ref) val_binding bindings }
    
    and interface_scope = { parent: scope option ref
                          , interface: interface ref
                          , interfaces: interface ref itf_binding bindings
                          , mods: (interface ref, mod ref) mod_binding bindings
                          , types: typ ref type_binding bindings
                          , vals: (typ ref, expr ref) val_binding bindings }

    and type_scope = { parent: scope option ref
                     , typ: typ ref
                     , types: typ ref type_binding bindings }

    and expr_scope = { parent: scope option ref
                     , expr: expr ref
                     , vals: (typ ref, expr ref) val_binding bindings }
    
    val scopeParent =
        fn ItfScope {parent, ...} => !parent
         | ModScope {parent, ...} => !parent
         | TypeScope {parent, ...} => !parent
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

    type ov = scope TypeVars.ov
    type uv = (scope, typ) TypeVars.uv

    val ovEq = TypeVars.ovEq scopeEq
    val uvMerge = TypeVars.uvMerge compareScopes
end

structure TypecheckingCst = Typechecking(struct
    structure Input = Cst
    structure Output = FAst
end)

