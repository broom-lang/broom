structure FAst = struct
    structure Type = FType(type var = Name.t)

    structure Term = struct
        type 'typ def = {var: Name.t, typ: 'typ}

        datatype ('typ, 'expr) expr = Fn of Pos.t * 'typ def * 'expr
                                    | TFn of Pos.t * Type.def * 'expr
                                    | App of Pos.t * {callee: 'expr, arg: 'expr}
                                    | TApp of Pos.t * {callee: 'expr, arg: 'typ}
                                    | Let of Pos.t * ('typ, 'expr) stmt vector * 'expr
                                    | Use of Pos.t * 'typ def
                                    | Const of Pos.t * Const.t

        and ('typ, 'expr) stmt = Val of Pos.t * 'typ def * 'expr
                               | Expr of 'expr
    end
end

