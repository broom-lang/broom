structure FAst = struct
    structure Type = NameFType

    structure Term = struct
        type 'typ def = {var: Name.t, typ: 'typ}

        datatype ('typ, 'expr) expr = Fn of Pos.t * 'typ def * 'expr
                                    | TFn of Pos.t * Type.def * 'expr
                                    | App of Pos.t * 'typ * {callee: 'expr, arg: 'expr}
                                    | TApp of Pos.t * 'typ * {callee: 'expr, arg: 'typ}
                                    | Let of Pos.t * ('typ, 'expr) stmt vector * 'expr
                                    | Type of Pos.t * 'typ
                                    | Use of Pos.t * 'typ def
                                    | Const of Pos.t * Const.t

        and ('typ, 'expr) stmt = Val of Pos.t * 'typ def * 'expr
                               | Expr of 'expr

        val exprPos =
            fn Fn (pos, _, _) => pos
             | TFn (pos, _, _) => pos
             | App (pos, _, _) => pos
             | TApp (pos, _, _) => pos
             | Let (pos, _, _) => pos
             | Type (pos, _) => pos
             | Use (pos, _) => pos
             | Const (pos, _) => pos

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
            | Type (_, t) => "[" ^ typeToString t ^ "]"
            | Use (_, {var, ...}) => Name.toString var 
            | Const (_, c) => Const.toString c

        fun typeOf fixType unfixExpr =
            let val fixed = fn Either.Left unfixed => fixType unfixed
                             | Either.Right fixed => fixed
                val rec typeOf =
                    fn Fn (pos, {typ = domain, ...}, body) =>
                        Either.Left (Type.Arrow (pos, { domain
                                                      , codomain = fixed (typeOf (unfixExpr body))}))
                     | TFn (pos, param, body) =>
                        Either.Left (Type.ForAll (pos, param, fixed (typeOf (unfixExpr body))))
                     | App (_, typ, _) => Either.Right typ
                     | TApp (_, typ, _) => Either.Right typ
                     | Let (_, _, body) => typeOf (unfixExpr body)
                     | Type (pos, t) => Either.Left (Type.Type (pos, t))
                     | Use (_, {typ, ...}) => Either.Right typ
                     | Const (pos, c) => Either.Left (Type.Prim (pos, Const.typeOf c))
            in fixed o typeOf
            end
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

        datatype expr = Fix of (Type.typ, expr) FAst.Term.expr
        
        type stmt = (Type.typ, expr) FAst.Term.stmt

        fun exprToString (Fix expr) = FAst.Term.exprToString Type.toString exprToString expr

        fun stmtToString stmt = FAst.Term.stmtToString Type.toString exprToString stmt
    end
end

