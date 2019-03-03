(* TODO: expr return types so that CPS transform can just grab them when it needs to *)

structure FAst = struct
    structure Type = Cst.Type

    structure Term = struct
        type 'typ def = {var: Name.t, typ: 'typ}

        datatype ('typ, 'expr) expr = Fn of Pos.t * 'typ def * 'expr
                                    | TFn of Pos.t * Type.def * 'expr
                                    | App of Pos.t * 'typ * {callee: 'expr, arg: 'expr}
                                    | TApp of Pos.t * 'typ * {callee: 'expr, arg: 'typ}
                                    | Let of Pos.t * ('typ, 'expr) stmt vector * 'expr
                                    | Use of Pos.t * 'typ def
                                    | Const of Pos.t * Const.t

        and ('typ, 'expr) stmt = Val of Pos.t * 'typ def * 'expr
                               | Expr of 'expr

       fun defToString typeToString {var, typ} = Name.toString var ^ ": " ^ typeToString typ

       fun stmtToString typeToString exprToString =
           fn Val (_, def, valExpr) =>
               "val " ^ defToString typeToString def ^ " = " ^ exprToString valExpr
            | Expr expr => exprToString expr

       fun exprToString typeToString exprToString =
           fn Fn (_, param, body) =>
               "\\" ^ defToString typeToString param ^ " => " ^ exprToString body
            | TFn (_, param, body) =>
               "/\\" ^ Type.defToString param ^ " => " ^ exprToString body
            | App (_, _, {callee, arg}) =>
               "(" ^ exprToString callee ^ " " ^ exprToString arg ^ ")"
            | TApp (_, _, {callee, arg}) =>
               "(" ^ exprToString callee ^ " [" ^ typeToString arg ^ "])" 
            | Let (_, stmts, body) =>
               let fun step (stmt, acc) = acc ^ stmtToString typeToString exprToString stmt ^ "\n"
               in "let " ^ Vector.foldl step "" stmts ^ "in\n" ^
                      "    " ^ exprToString body ^ "\nend"
               end
            | Use (_, {var, ...}) => Name.toString var 
            | Const (_, c) => Const.toString c

        fun typeOf fixType unfixExpr =
            let val rec typeOf =
                    fn Fn (pos, {typ = domain, ...}, body) =>
                        fixType (Type.Arrow (pos, {domain, codomain = typeOf (unfixExpr body)}))
                     | TFn (pos, param, body) =>
                        fixType (Type.ForAll (pos, param, typeOf (unfixExpr body)))
                     | App (_, typ, _) => typ
                     | TApp (_, typ, _) => typ
                     | Let (_, _, body) => typeOf (unfixExpr body)
                     | Use (_, {typ, ...}) => typ
                     | Const (pos, c) => fixType (Type.Prim (pos, Const.typeOf c))
            in typeOf
            end
    end
end

