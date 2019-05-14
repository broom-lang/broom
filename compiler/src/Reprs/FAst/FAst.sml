structure FAst = struct
    structure Type = FType

    structure Term = struct
        type 'typ def = {var: Name.t, typ: 'typ}

        datatype 'typ expr = Fn of Pos.t * 'typ def * 'typ expr
                           | TFn of Pos.t * Type.def * 'typ expr
                           | Extend of Pos.t * 'typ * (Name.t * 'typ expr) vector * 'typ expr option
                           | App of Pos.t * 'typ * {callee: 'typ expr, arg: 'typ expr}
                           | TApp of Pos.t * 'typ * {callee: 'typ expr, arg: 'typ}
                           | Field of Pos.t * 'typ * 'typ expr * Name.t
                           | Let of Pos.t * 'typ stmt vector * 'typ expr
                           | Type of Pos.t * 'typ
                           | Use of Pos.t * 'typ def
                           | Const of Pos.t * Const.t

        and 'typ stmt = Val of Pos.t * 'typ def * 'typ expr
                      | Expr of 'typ expr

        val exprPos =
            fn Fn (pos, _, _) => pos
             | TFn (pos, _, _) => pos
             | Extend (pos, _, _, _) => pos
             | App (pos, _, _) => pos
             | TApp (pos, _, _) => pos
             | Field (pos, _, _, _) => pos
             | Let (pos, _, _) => pos
             | Type (pos, _) => pos
             | Use (pos, _) => pos
             | Const (pos, _) => pos

       fun defToString typeToString {var, typ} = Name.toString var ^ ": " ^ typeToString typ

       fun stmtToString typeToString =
           fn Val (_, def, valExpr) =>
               "val " ^ defToString typeToString def ^ " = " ^ exprToString typeToString valExpr
            | Expr expr => exprToString typeToString expr

       and exprToString typeToString =
           fn Fn (_, param, body) =>
               "\\" ^ defToString typeToString param ^ " => " ^ exprToString typeToString body
            | TFn (_, param, body) =>
               "/\\" ^ Type.defToString param ^ " => " ^ exprToString typeToString body
            | Extend (_, _, fields, record) =>
               "{" ^ getOpt (Option.map (exprToString typeToString) record, "")
                   ^ " with " ^ fieldExprsToString typeToString fields ^ "}"
            | App (_, _, {callee, arg}) =>
               "(" ^ exprToString typeToString callee ^ " " ^ exprToString typeToString arg ^ ")"
            | TApp (_, _, {callee, arg}) =>
               "(" ^ exprToString typeToString callee ^ " [" ^ typeToString arg ^ "])" 
            | Field (_, _, expr, label) =>
               "(" ^ exprToString typeToString expr ^ "." ^ Name.toString label ^ ")"
            | Let (_, stmts, body) =>
               let fun step (stmt, acc) = acc ^ stmtToString typeToString stmt ^ "\n"
               in "let " ^ Vector.foldl step "" stmts ^ "in\n" ^
                      "    " ^ exprToString typeToString body ^ "\nend"
               end
            | Type (_, t) => "[" ^ typeToString t ^ "]"
            | Use (_, {var, ...}) => Name.toString var 
            | Const (_, c) => Const.toString c

        and fieldExprsToString typeToString fields =
            let fun step ((label, expr), acc) =
                    acc ^ ", " ^ Name.toString label ^ " = " ^ exprToString typeToString expr
            in Vector.foldl step "" fields
            end

        fun typeOf (fixT: 'typ Type.typ -> 'typ): 'typ expr -> 'typ =
            fn Fn (pos, {typ = domain, ...}, body) =>
                fixT (Type.Arrow (pos, {domain, codomain = typeOf fixT body}))
             | TFn (pos, param, body) =>
                fixT (Type.ForAll (pos, param, typeOf fixT body))
             | Extend (_, typ, _, _) | App (_, typ, _) | TApp (_, typ, _) => typ
             | Field (_, typ, _, _) => typ
             | Let (_, _, body) => typeOf fixT body
             | Type (pos, t) => fixT (Type.Type (pos, t))
             | Use (_, {typ, ...}) => typ
             | Const (pos, c) => fixT (Type.Prim (pos, Const.typeOf c))

        datatype 'typ binder = ValueBinder of 'typ def * 'typ expr option
                             | TypeBinder of Type.def * 'typ option

        fun foldBinders f acc =
            fn Fn (_, def, _) => f (ValueBinder (def, NONE), acc)
             | TFn (_, def, _) => f (TypeBinder (def, NONE), acc)
             | Let (_, stmts, _) =>
                Vector.foldl (fn (Val (_, def, expr), acc) => f (ValueBinder (def, SOME expr), acc)
                               | (Expr _, acc) => acc)
                             acc stmts
             | Extend _ | App _ | TApp _ | Field _ | Type _ | Use _ | Const _ => acc
    end
end

structure FixedFAst = struct
    structure Type = struct
        open FAst.Type

        datatype typ = Fix of typ FAst.Type.typ

        fun toString (Fix t) = FAst.Type.toString toString t
    end

    structure Term = struct
        open FAst.Term

        type expr = Type.typ FAst.Term.expr

        val toString = FAst.Term.exprToString Type.toString
    end
end

