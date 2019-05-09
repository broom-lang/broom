structure Cst = struct
    structure Type = struct
        datatype prim = datatype NameFType.prim

        datatype ('typ, 'expr) typ = Arrow of Pos.t * {domain: 'typ, codomain: 'typ}
                                   | Singleton of Pos.t * 'expr
                                   | Path of 'expr
                                   | Prim of Pos.t * prim

        val primToString = NameFType.primToString

        fun toString toString exprToString =
            fn Arrow (_, {domain, codomain}) =>
                toString domain ^ " -> " ^ toString codomain
             | Singleton (_, expr) => "(= " ^ exprToString expr ^ ")"
             | Path expr => exprToString expr
             | Prim (_, p) => primToString p

        fun pos exprPos =
            fn Arrow (pos, _) => pos
             | Singleton (pos, _) => pos
             | Path expr => exprPos expr
             | Prim (pos, _) => pos

        fun shallowFoldl f acc =
            fn Arrow (_, {domain, codomain}) => f (codomain, f (domain, acc))

        fun rowExtTail {wrap, tail = _} t = wrap t
    end

    structure Term = struct    
        datatype ('typ, 'expr) stmt
            = Val of Pos.t * Name.t * 'typ option * 'expr
            | Expr of 'expr
    
        datatype ('typ, 'expr) expr
            = Fn of Pos.t * Name.t * 'typ option * 'expr
            | Let of Pos.t * ('typ, 'expr) stmt vector * 'expr
            | Record of Pos.t * 'expr row
            | App of Pos.t * {callee: 'expr, arg: 'expr}
            | Field of Pos.t * 'expr * Name.t
            | Ann of Pos.t * 'expr * 'typ
            | Type of Pos.t * 'typ
            | Use of Pos.t * Name.t
            | Const of Pos.t * Const.t
        withtype 'expr row = (Name.t * 'expr) vector

        val exprPos =
            fn Fn (pos, _, _, _) => pos
             | Let (pos, _, _) => pos
             | Record (pos, _) => pos
             | App (pos, _) => pos
             | Field (pos, _, _) => pos
             | Ann (pos, _, _) => pos
             | Type (pos, _) => pos
             | Use (pos, _) => pos
             | Const (pos, _) => pos

        fun stmtToString typeToString exprToString =
            fn Val (_, name, maybeAnn, valExpr) =>
                "val " ^ Name.toString name ^
                    (case maybeAnn
                     of SOME ann => ": " ^ typeToString ann
                      | NONE => "") ^
                    " = " ^ exprToString valExpr
             | Expr expr => exprToString expr

        fun rowToString exprToString row =
            let fun step ((label, expr), acc) =
                    acc ^ " " ^ Name.toString label ^ " = " ^ exprToString expr ^ ","
            in Vector.foldl step "" row
            end

        fun exprToString typeToString exprToString =
            fn Fn (_, param, maybeAnn, body) =>
                "fn " ^ Name.toString param ^
                    (case maybeAnn
                     of SOME t => ": " ^ typeToString t
                      | NONE => "") ^
                    " => " ^ exprToString body
             | Record (_, row) => "{" ^ rowToString exprToString row ^ "}"
             | App (_, {callee, arg}) =>
                "(" ^ exprToString callee ^ " " ^ exprToString arg ^ ")"
             | Field (_, expr, label) => "(" ^ exprToString expr ^ "." ^ Name.toString label ^ ")"
             | Let (_, stmts, body) =>
                let fun step (stmt, acc) = acc ^ stmtToString typeToString exprToString stmt ^
                "\n"
                in "let " ^ Vector.foldl step "" stmts ^ "in\n" ^
                       "    " ^ exprToString body ^ "\nend"
                end
             | Ann (_, expr, t) => exprToString expr ^ ": " ^ typeToString t
             | Type (_, t) => "type " ^ typeToString t
             | Use (_, name) => Name.toString name
             | Const (_, c) => Const.toString c
    end
end

structure FixedCst = struct
    datatype typ' = FixT of (typ', expr') Cst.Type.typ
    and expr' = Fix of (typ', expr') Cst.Term.expr

    fun typeToString' (FixT t) = Cst.Type.toString typeToString' exprToString' t
    and exprToString' (Fix expr) = Cst.Term.exprToString typeToString' exprToString' expr 

    structure Type = struct
        open Cst.Type
 
        datatype typ = datatype typ'
        
        val toString = typeToString'
    end

    structure Term = struct
        open Cst.Term

        datatype expr = datatype expr'
        
        type stmt = (Type.typ, expr) Cst.Term.stmt

        val exprToString = exprToString'

        fun stmtToString stmt = Cst.Term.stmtToString Type.toString exprToString stmt
    end
end

