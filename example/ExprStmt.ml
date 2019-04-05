structure Expr = struct
    datatype expr = Fn of string * expr
                  | App of expr * expr
                  | Block of Stmt.stmt list * expr
                  | Var of string

    val toString =
        fn Fn (param, body) => "fn " ^ param ^ " . " ^ toString body
         | App (callee, arg) => "(" ^ toString callee ^ " " ^ toString arg ^ ")"
         | Block (stmts, expr) =>
            let fun step (acc, stmt) = acc ^ Stmt.toString stmt ^ "; "
            in "begin " ^ List.foldl step "" stmts ^ "; " ^ toString expr ^ " end"
            end
         | Var name => name
end

structure Stmt = struct
    datatype stmt = Def of string * expr
                  | Expr of Expr.expr

    val toString =
        fn Def (name, expr) => name ^ " = " ^ Expr.toString expr
         | Expr expr => Expr.toString expr
end

