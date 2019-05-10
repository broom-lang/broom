structure FAst = struct
    structure Type = NameFType

    structure Term = struct
        type 'typ def = {var: Name.t, typ: 'typ}

        datatype ('typ, 'expr) expr = Fn of Pos.t * 'typ def * 'expr
                                    | TFn of Pos.t * Type.def * 'expr
                                    | Extend of Pos.t * 'typ * (Name.t * 'expr) vector * 'expr option
                                    | App of Pos.t * 'typ * {callee: 'expr, arg: 'expr}
                                    | TApp of Pos.t * 'typ * {callee: 'expr, arg: 'typ}
                                    | Field of Pos.t * 'typ * 'expr * Name.t
                                    | Let of Pos.t * ('typ, 'expr) stmt vector * 'expr
                                    | Type of Pos.t * 'typ
                                    | Use of Pos.t * 'typ def
                                    | Const of Pos.t * Const.t

        and ('typ, 'expr) stmt = Val of Pos.t * 'typ def * 'expr
                               | Expr of 'expr

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

       fun stmtToString typeToString exprToString =
           fn Val (_, def, valExpr) =>
               "val " ^ defToString typeToString def ^ " = " ^ exprToString valExpr
            | Expr expr => exprToString expr

       fun exprToString typeToString exprToString =
           fn Fn (_, param, body) =>
               "\\" ^ defToString typeToString param ^ " => " ^ exprToString body
            | TFn (_, param, body) =>
               "/\\" ^ Type.defToString param ^ " => " ^ exprToString body
            | Extend (_, _, fields, record) =>
               "{" ^ getOpt (Option.map exprToString record, "")
                   ^ " with " ^ fieldExprsToString exprToString fields ^ "}"
            | App (_, _, {callee, arg}) =>
               "(" ^ exprToString callee ^ " " ^ exprToString arg ^ ")"
            | TApp (_, _, {callee, arg}) =>
               "(" ^ exprToString callee ^ " [" ^ typeToString arg ^ "])" 
            | Field (_, _, expr, label) =>
               "(" ^ exprToString expr ^ "." ^ Name.toString label ^ ")"
            | Let (_, stmts, body) =>
               let fun step (stmt, acc) = acc ^ stmtToString typeToString exprToString stmt ^ "\n"
               in "let " ^ Vector.foldl step "" stmts ^ "in\n" ^
                      "    " ^ exprToString body ^ "\nend"
               end
            | Type (_, t) => "[" ^ typeToString t ^ "]"
            | Use (_, {var, ...}) => Name.toString var 
            | Const (_, c) => Const.toString c

        and fieldExprsToString exprToString fields =
            let fun step ((label, expr), acc) =
                    acc ^ ", " ^ Name.toString label ^ " = " ^ exprToString expr
            in Vector.foldl step "" fields
            end

        fun typeOf fixType unfixExpr =
            let val fixed = fn Either.Left unfixed => fixType unfixed
                             | Either.Right fixed => fixed
                val rec typeOf =
                    fn Fn (pos, {typ = domain, ...}, body) =>
                        Either.Left (Type.Arrow (pos, { domain
                                                      , codomain = fixed (typeOf (unfixExpr body))}))
                     | TFn (pos, param, body) =>
                        Either.Left (Type.ForAll (pos, param, fixed (typeOf (unfixExpr body))))
                     | Extend (_, typ, _, _) | App (_, typ, _) | TApp (_, typ, _) => Either.Right typ
                     | Field (_, typ, _, _) => Either.Right typ
                     | Let (_, _, body) => typeOf (unfixExpr body)
                     | Type (pos, t) => Either.Left (Type.Type (pos, t))
                     | Use (_, {typ, ...}) => Either.Right typ
                     | Const (pos, c) => Either.Left (Type.Prim (pos, Const.typeOf c))
            in fixed o typeOf
            end

        datatype ('typ, 'expr) Binder = ValueBinder of 'typ def * 'expr option
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

        datatype expr = Fix of (Type.typ, expr) FAst.Term.expr
        
        fun exprToString (Fix expr) = FAst.Term.exprToString Type.toString exprToString expr
    end
end

