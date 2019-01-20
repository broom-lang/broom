signature TYPECHECKER_INPUT = sig
    type kind
    type 'typ typ
    type ('typ, 'expr) expr
    type ('itf, 'typ) interface
    type ('itf, 'mod, 'typ, 'expr) mod
end

signature TYPECHECKER_OUTPUT = TYPECHECKER_INPUT

functor Typechecking(Puts: sig
    structure Input: TYPECHECKER_INPUT
    structure Output: TYPECHECKER_OUTPUT
end) = struct
    structure Input = Puts.Input
    structure Output = Puts.Output

    type 'b bindings = 'b NameHashTable.hash_table

    type 'typ type_binding = { kind: Input.kind
		             , typ: 'typ option }

    type ('typ, 'expr) val_binding = { typ: 'typ
                                     , value: 'expr option }

    type 'itf itf_binding = { interface: 'itf }

    type ('itf, 'mod) mod_binding = { interface: 'itf
                                    , mod: 'mod option }

    datatype typ = InputType of typ ref Input.typ
                 | OutputType of typ ref Output.typ
                 | ScopeType of type_scope
    
    and expr = InputExpr of (typ ref, expr ref) Input.expr
             | OutputExpr of (typ ref, expr ref) Output.expr
             | ScopeExpr of expr_scope

    and interface = InputItf of (interface ref, typ ref) Input.interface
                  | OutputItf of typ ref Output.typ
                  | ScopeItf of interface_scope

    and mod = InputMod of (interface ref, mod ref, typ ref, expr ref) Input.mod
            | OutputMod of (typ ref, expr ref) Output.expr
            | ScopeMod of mod_scope

    and scope = ItfScope of interface_scope
              | ModScope of mod_scope
              | TypeScope of type_scope
              | ExprScope of expr_scope

    and mod_scope = FixModScope of { parent: mod_scope
                                   , mod: mod ref
				   , interfaces: interface ref itf_binding bindings
                                   , mods: (interface ref, mod ref) mod_binding bindings
	                           , types: typ ref type_binding bindings
                                   , vals: (typ ref, expr ref) val_binding bindings }
    
    withtype interface_scope = { parent: scope
                               , interface: interface ref
                               , interfaces: interface ref itf_binding bindings
                               , mods: (interface ref, mod ref) mod_binding bindings
                               , types: typ ref type_binding bindings
                               , vals: (typ ref, expr ref) val_binding bindings }

    and type_scope = { parent: scope
                     , typ: typ ref
                     , types: typ ref type_binding bindings }

    and expr_scope = { parent: scope
                     , expr: expr ref
                     , vals: (typ ref, expr ref) val_binding bindings }

end

structure TypecheckingCstInput = struct
    type kind = Cst.Type.kind
    type 'typ typ = 'typ Cst.Type.typ
    type ('typ, 'expr) expr = ('typ, 'expr) Cst.Term.expr
    type ('itf, 'typ) interface = ('itf, 'typ) Cst.Interface.interface
    type ('itf, 'mod, 'typ, 'expr) mod = ('itf, 'mod, 'typ, 'expr) Cst.Module.mod
end

structure TypecheckingCst = Typechecking(struct
    structure Input = TypecheckingCstInput
    structure Output = TypecheckingCstInput (* FIXME *)
end)

