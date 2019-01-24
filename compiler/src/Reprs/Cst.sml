structure Cst = struct
    structure Type = FType(Name)

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

        fun stmtToString typeToString exprToString =
            fn Val (_, name, maybeAnn, valExpr) =>
                "val " ^ Name.toString name ^
                    (case maybeAnn
                     of SOME ann => ": " ^ typeToString ann
                      | NONE => "") ^
                    " = " ^ exprToString valExpr
             | Expr expr => exprToString expr

        fun exprToString typeToString exprToString =
            fn Fn (_, param, maybeAnn, body) =>
                "fn " ^ Name.toString param ^
                    (case maybeAnn
                     of SOME t => ": " ^ typeToString t
                      | NONE => "") ^
                    " => " ^ exprToString body
             | App (_, {callee, arg}) =>
                "(" ^ exprToString callee ^ " " ^ exprToString arg ^ ")"
             | Let (_, stmts, body) =>
                let fun step (stmt, acc) = acc ^ stmtToString typeToString exprToString stmt ^
                "\n"
                in "let " ^ Vector.foldl step "" stmts ^ "in\n" ^
                       "    " ^ exprToString body ^ "\nend"
                end
             | Ann (_, expr, t) => exprToString expr ^ ": " ^ typeToString t
             | Use (_, name) => Name.toString name
             | Const (_, c) => Const.toString c
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
        open Cst.Type

        datatype typ = Fix of typ Cst.Type.typ

        fun toString (Fix t) = Cst.Type.toString toString t
    end

    structure Term = struct
        open Cst.Term

        datatype expr = Fix of (Type.typ, expr) Cst.Term.expr
        
        type stmt = (Type.typ, expr) Cst.Term.stmt

        fun exprToString (Fix expr) = Cst.Term.exprToString Type.toString exprToString expr

        fun stmtToString stmt = Cst.Term.stmtToString Type.toString exprToString stmt
    end

    structure Interface = struct
        open Cst.Interface

        datatype interface = Fix of (interface, Type.typ) Cst.Interface.interface
        
        type decl = (interface, Type.typ) Cst.Interface.decl
    end

    structure Module = struct
        open Cst.Module

        datatype mod = Fix of (Interface.interface, mod, Type.typ, Term.expr) Cst.Module.mod

        type def = (Interface.interface, mod, Type.typ, Term.expr) Cst.Module.def
    end
end

