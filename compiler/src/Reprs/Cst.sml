structure Cst = struct
    structure Type = FType(type var = Name.t)

    structure Term = struct    
        datatype ('typ, 'expr) stmt
            = Val of Pos.t * Name.t * 'typ option * 'expr
            | Expr of 'expr
    
        datatype ('typ, 'expr) expr
            = Fn of Pos.t * Name.t * 'typ option * 'expr
            | Let of Pos.t * ('typ, 'expr) stmt vector * 'expr
            | App of Pos.t * {callee: 'expr, arg: 'expr}
            | Ann of Pos.t * 'expr * 'typ
            | Use of Pos.t * Name.t
            | Const of Pos.t * Const.t
    end

    structure Interface = struct
        datatype ('itf, 'typ) decl
            = DInt of Pos.t * Name.t * Name.t vector * 'itf
            | DMod of Pos.t * Name.t * 'itf
            | DTyp of Pos.t * Name.t * Name.t vector * 'typ option
            | DVal of Pos.t * Name.t * 'typ

        datatype ('itf, 'typ) interface =
            Interface of Pos.t * ('itf, 'typ) decl vector
    end

    structure Module = struct
	datatype ('itf, 'mod, 'typ, 'expr) def 
            = Int of Pos.t * Name.t * Name.t vector * 'itf
            | Mod of Pos.t * Name.t * 'itf option * 'mod
            | Typ of Pos.t * Name.t * Name.t vector * 'typ
            | Val of Pos.t * Name.t * 'typ option * 'expr

        datatype ('itf, 'mod, 'typ, 'expr) mod =
            Module of Pos.t * ('itf, 'mod, 'typ, 'expr) def vector
    end
end

structure FixedCst = struct
    structure Type = struct
        datatype typ = Fix of typ Cst.Type.typ
    end

    structure Term = struct
        datatype expr = Fix of (Type.typ, expr) Cst.Term.expr
        
        type stmt = (Type.typ, expr) Cst.Term.stmt
    end

    structure Interface = struct
        datatype interface = Fix of (interface, Type.typ) Cst.Interface.interface
        
        type decl = (interface, Type.typ) Cst.Interface.decl
    end

    structure Module = struct
        datatype mod = Fix of (Interface.interface, mod, Type.typ, Term.expr) Cst.Module.mod

        type def = (Interface.interface, mod, Type.typ, Term.expr) Cst.Module.def
    end
end

