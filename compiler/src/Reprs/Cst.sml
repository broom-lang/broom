structure Cst = struct
    structure Type :> sig
        structure Prim: PRIM_TYPE

        datatype 'expr typ = Arrow of Pos.t * {domain: 'expr typ, codomain: 'expr typ}
                           | Record of Pos.t * 'expr typ
                           | RowExt of Pos.t * 'expr row_ext
                           | EmptyRow of Pos.t
                           | Singleton of Pos.t * 'expr
                           | Path of 'expr
                           | Prim of Pos.t * Prim.t

        withtype 'expr row_ext = {field: Name.t * 'expr typ, ext: 'expr typ}

        val toString: ('expr -> string) -> 'expr typ -> string
        val pos: ('expr -> Pos.t) -> 'expr typ -> Pos.t
        val shallowFoldl: ('expr typ * 'a -> 'a) -> 'a -> 'expr typ -> 'a
        val rowExtTail: 'expr typ -> 'expr typ
    end = struct
        structure Prim = PrimType

        datatype 'expr typ = Arrow of Pos.t * {domain: 'expr typ, codomain: 'expr typ}
                           | Record of Pos.t * 'expr typ
                           | RowExt of Pos.t * 'expr row_ext
                           | EmptyRow of Pos.t
                           | Singleton of Pos.t * 'expr
                           | Path of 'expr
                           | Prim of Pos.t * Prim.t

        withtype 'expr row_ext = {field: Name.t * 'expr typ, ext: 'expr typ}

        fun toString exprToString t =
            let val rec toString = fn Arrow (_, {domain, codomain}) =>
                                       toString domain ^ " -> " ^ toString codomain
                                    | Record (_, row) => "{" ^ toString row ^ "}" (* TODO: Extend to `Extend` as in FAst. *)
                                    | RowExt (_, {field = (label, fieldt), ext}) =>
                                       Name.toString label ^ ": " ^ toString fieldt ^ " | " ^ toString ext
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
        datatype ('bt, 'be) stmt = Val of Pos.t * Name.t * 'bt * 'be
                                 | Expr of ('bt, 'be) expr
    
        and ('bt, 'be) expr = Fn of Pos.t * Name.t * 'bt * ('bt, 'be) expr
                            | Let of Pos.t * ('bt, 'be) stmt vector * ('bt, 'be) expr
                            | Record of Pos.t * ('bt, 'be) row
                            | App of Pos.t * {callee: ('bt, 'be) expr, arg: ('bt, 'be) expr}
                            | Field of Pos.t * ('bt, 'be) expr * Name.t
                            | Ann of Pos.t * ('bt, 'be) expr * ('bt, 'be) expr Type.typ
                            | Type of Pos.t * ('bt, 'be) expr Type.typ
                            | Use of Pos.t * Name.t
                            | Const of Pos.t * Const.t

        withtype ('bt, 'be) row = (Name.t * ('bt, 'be) expr) vector

        val exprPos: ('bt, 'be) expr -> Pos.t
        val exprToString: ('bt -> string) -> ('be -> string) -> ('bt, 'be) expr -> string
        val stmtToString: ('bt -> string) -> ('be -> string) -> ('bt, 'be) stmt -> string
    end = struct
        datatype ('bt, 'be) stmt = Val of Pos.t * Name.t * 'bt * 'be
                                 | Expr of ('bt, 'be) expr
    
        and ('bt, 'be) expr = Fn of Pos.t * Name.t * 'bt * ('bt, 'be) expr
                            | Let of Pos.t * ('bt, 'be) stmt vector * ('bt, 'be) expr
                            | Record of Pos.t * ('bt, 'be) row
                            | App of Pos.t * {callee: ('bt, 'be) expr, arg: ('bt, 'be) expr}
                            | Field of Pos.t * ('bt, 'be) expr * Name.t
                            | Ann of Pos.t * ('bt, 'be) expr * ('bt, 'be) expr Type.typ
                            | Type of Pos.t * ('bt, 'be) expr Type.typ
                            | Use of Pos.t * Name.t
                            | Const of Pos.t * Const.t

        withtype ('bt, 'be) row = (Name.t * ('bt, 'be) expr) vector

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

        fun stmtToString (btToString: 'bt -> string) (beToString: 'be -> string): ('bt, 'be) stmt -> string =
            fn Val (_, name, ann, valExpr) =>
                "val " ^ Name.toString name ^ btToString ann ^ " = " ^ beToString valExpr
             | Expr expr => exprToString btToString beToString expr

        and rowToString exprToString row =
            let fun step ((label, expr), acc) =
                    acc ^ " " ^ Name.toString label ^ " = " ^ exprToString expr ^ ","
            in Vector.foldl step "" row
            end

        and exprToString (btToString: 'bt -> string) (beToString: 'be -> string) expr: string =
            let val rec toString = fn Fn (_, param, ann, body) =>
                                       "fn " ^ Name.toString param ^ btToString ann ^ " => " ^ toString body
                                    | Record (_, row) => "{" ^ rowToString toString row ^ "}"
                                    | App (_, {callee, arg}) =>
                                       "(" ^ toString callee ^ " " ^ toString arg ^ ")"
                                    | Field (_, expr, label) => "(" ^ toString expr ^ "." ^ Name.toString label ^ ")"
                                    | Let (_, stmts, body) =>
                                       let fun step (stmt, acc) = acc ^ stmtToString btToString beToString stmt ^
                                       "\n"
                                       in "let " ^ Vector.foldl step "" stmts ^ "in\n" ^
                                             "    " ^ toString body ^ "\nend"
                                       end
                                    | Ann (_, expr, t) => toString expr ^ ": " ^ Type.toString toString t
                                    | Type (_, t) => "type " ^ Type.toString toString t
                                    | Use (_, name) => Name.toString name
                                    | Const (_, c) => Const.toString c
            in toString expr
            end
    end
end

structure FixedCst = struct
    datatype typ' = FixT of (typ' option, expr') Cst.Term.expr Cst.Type.typ
    and expr' = Fix of (typ' option, expr') Cst.Term.expr

    fun typeToString' (FixT t) =
         Cst.Type.toString (Cst.Term.exprToString (Option.toString typeToString') exprToString') t
    and exprToString' (Fix expr) = Cst.Term.exprToString (Option.toString typeToString') exprToString' expr 

    structure Type = struct
        open Cst.Type
 
        datatype ftyp = datatype typ'
        
        val toString = typeToString'
    end

    structure Term = struct
        open Cst.Term

        datatype fexpr = datatype expr'
        
        type stmt = (Type.ftyp option, fexpr) Cst.Term.stmt

        val exprToString = exprToString'
    end
end

