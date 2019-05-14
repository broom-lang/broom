structure Cst = struct
    structure Type :> sig
        structure Prim: PRIM_TYPE

        datatype ('typ, 'expr) typ = Arrow of Pos.t * {domain: 'typ, codomain: 'typ}
                                   | Record of Pos.t * 'typ
                                   | RowExt of Pos.t * ('typ, 'expr) row_ext
                                   | EmptyRow of Pos.t
                                   | Singleton of Pos.t * 'expr
                                   | Path of 'expr
                                   | Prim of Pos.t * Prim.t

        withtype ('typ, 'expr) row_ext = {field: Name.t * 'typ, ext: 'typ}

        val toString: ('typ -> string) -> ('expr -> string) -> ('typ, 'expr) typ -> string
        val pos: ('expr -> Pos.t) -> ('typ, 'expr) typ -> Pos.t
        val shallowFoldl: ('typ * 'a -> 'a) -> 'a -> ('typ, 'expr) typ -> 'a
        val rowExtTail: ('typ, 'expr) typ -> ('typ, 'expr) typ
    end = struct
        structure Prim = PrimType

        datatype ('typ, 'expr) typ = Arrow of Pos.t * {domain: 'typ, codomain: 'typ}
                                   | Record of Pos.t * 'typ
                                   | RowExt of Pos.t * ('typ, 'expr) row_ext
                                   | EmptyRow of Pos.t
                                   | Singleton of Pos.t * 'expr
                                   | Path of 'expr
                                   | Prim of Pos.t * Prim.t

        withtype ('typ, 'expr) row_ext = {field: Name.t * 'typ, ext: 'typ}

        fun toString typeToString exprToString t =
            let val rec toString = fn Arrow (_, {domain, codomain}) =>
                                       typeToString domain ^ " -> " ^ typeToString codomain
                                    | Record (_, row) => "{" ^ typeToString row ^ "}" (* TODO: Extend to `Extend` as in FAst. *)
                                    | RowExt (_, {field = (label, fieldt), ext}) =>
                                       Name.toString label ^ ": " ^ typeToString fieldt ^ " | " ^ typeToString ext
                                    | EmptyRow _ => "(||)"
                                    | Singleton (_, expr) => "(= " ^ exprToString expr ^ ")"
                                    | Path expr => exprToString expr
                                    | Prim (_, p) => Prim.toString p
            in toString t
            end

        fun pos exprPos =
            fn Arrow (pos, _) => pos
             | Singleton (pos, _) => pos
             | Path expr => exprPos expr
             | Prim (pos, _) => pos

        fun shallowFoldl f acc =
            fn Arrow (_, {domain, codomain}) => f (codomain, f (domain, acc))

        fun rowExtTail t = t
    end

    structure Term :> sig
        datatype ('typ, 'bt, 'expr, 'be) stmt = Val of Pos.t * Name.t * 'bt * 'be
                                       | Expr of 'expr
    
        and ('typ, 'bt, 'expr, 'be) expr = Fn of Pos.t * Name.t * 'bt * 'expr
                            | Let of Pos.t * ('typ, 'bt, 'expr, 'be) stmt vector * 'expr
                            | Record of Pos.t * 'expr row
                            | App of Pos.t * {callee: 'expr, arg: 'expr}
                            | Field of Pos.t * 'expr * Name.t
                            | Ann of Pos.t * 'expr * 'typ
                            | Type of Pos.t * 'typ
                            | Use of Pos.t * Name.t
                            | Const of Pos.t * Const.t

        withtype 'expr row = (Name.t * 'expr) vector

        val exprPos: ('typ, 'bt, 'expr, 'be) expr -> Pos.t
        val exprToString: ('typ -> string) -> ('bt -> string) -> ('expr -> string) -> ('be -> string)
                        -> ('typ, 'bt, 'expr, 'be) expr -> string
        val stmtToString: ('typ -> string) -> ('bt -> string) -> ('expr -> string) -> ('be -> string)
                        -> ('typ, 'bt, 'expr, 'be) stmt -> string
    end = struct
        datatype ('typ, 'bt, 'expr, 'be) stmt = Val of Pos.t * Name.t * 'bt * 'be
                                 | Expr of 'expr
    
        and ('typ, 'bt, 'expr, 'be) expr = Fn of Pos.t * Name.t * 'bt * 'expr
                            | Let of Pos.t * ('typ, 'bt, 'expr, 'be) stmt vector * 'expr
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

        fun stmtToString typeToString btToString exprToString beToString =
            fn Val (_, name, ann, valExpr) =>
                "val " ^ Name.toString name ^ btToString ann ^ " = " ^ beToString valExpr
             | Expr expr => exprToString expr

        fun rowToString exprToString row =
            let fun step ((label, expr), acc) =
                    acc ^ " " ^ Name.toString label ^ " = " ^ exprToString expr ^ ","
            in Vector.foldl step "" row
            end

        fun exprToString typeToString btToString exprToString beToString expr =
            let val rec toString = fn Fn (_, param, ann, body) =>
                                       "fn " ^ Name.toString param ^ btToString ann ^ " => " ^ exprToString body
                                    | Record (_, row) => "{" ^ rowToString exprToString row ^ "}"
                                    | App (_, {callee, arg}) =>
                                       "(" ^ exprToString callee ^ " " ^ exprToString arg ^ ")"
                                    | Field (_, expr, label) => "(" ^ exprToString expr ^ "." ^ Name.toString label ^ ")"
                                    | Let (_, stmts, body) =>
                                       let fun step (stmt, acc) = acc ^ stmtToString typeToString btToString exprToString beToString stmt ^
                                       "\n"
                                       in "let " ^ Vector.foldl step "" stmts ^ "in\n" ^
                                             "    " ^ exprToString body ^ "\nend"
                                       end
                                    | Ann (_, expr, t) => exprToString expr ^ ": " ^ typeToString t
                                    | Type (_, t) => "type " ^ typeToString t
                                    | Use (_, name) => Name.toString name
                                    | Const (_, c) => Const.toString c
            in toString expr
            end
    end
end

structure FixedCst = struct
    datatype typ' = FixT of (typ', expr') Cst.Type.typ
    and expr' = Fix of (typ', typ' option, expr', expr') Cst.Term.expr

    fun typeToString' (FixT t) = Cst.Type.toString typeToString' exprToString' t
    and exprToString' (Fix expr) = Cst.Term.exprToString typeToString' (Option.toString typeToString') exprToString' exprToString' expr 

    structure Type = struct
        open Cst.Type
 
        datatype ftyp = datatype typ'
        
        val toString = typeToString'
    end

    structure Term = struct
        open Cst.Term

        datatype fexpr = datatype expr'
        
        type stmt = (Type.ftyp, Type.ftyp option, fexpr, fexpr) Cst.Term.stmt

        val exprToString = exprToString'
    end
end

