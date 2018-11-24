structure Cst :> sig
    datatype type_ann = ForAll of Pos.t * Name.t * type_ann
                      | UseT of Pos.t * Name.t
                      | Arrow of Pos.t * {domain: type_ann, codomain: type_ann}
                      | Prim of Pos.t * Type.prim

    datatype expr = Fn of Pos.t * Name.t * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | Ann of Pos.t * expr * type_ann
                  | Use of Pos.t * Name.t
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * Name.t * expr

    val stmtToString: stmt -> string
    val exprToString: expr -> string
end = struct
    datatype type_ann = ForAll of Pos.t * Name.t * type_ann
                      | UseT of Pos.t * Name.t
                      | Arrow of Pos.t * {domain: type_ann, codomain: type_ann}
                      | Prim of Pos.t * Type.prim

    datatype expr = Fn of Pos.t * Name.t * expr
                  | App of Pos.t * {callee: expr, arg: expr}
                  | Ann of Pos.t * expr * type_ann
                  | Use of Pos.t * Name.t
                  | Const of Pos.t * Const.t

    and stmt = Def of Pos.t * Name.t * expr

    val rec typeAnnToString = fn ForAll (_, param, t) =>
                                  "forall " ^ Name.toString param ^ " . " ^ typeAnnToString t
                               | UseT (_, name) => Name.toString name
                               | Arrow (_, {domain, codomain}) =>
                                  typeAnnToString domain ^ " -> " ^ typeAnnToString codomain
                               | Prim (_, p) => Type.primToString p

    val rec stmtToString = fn Def (_, name, valExpr) =>
                               "val " ^ Name.toString name ^ " = " ^ exprToString valExpr
    and exprToString = fn Fn (_, param, body) =>
                           "fn " ^ Name.toString param ^ " => " ^ exprToString body
                        | App (_, {callee, arg}) =>
                           "(" ^ exprToString callee ^ " " ^ exprToString arg ^ ")"
                        | Ann (_, expr, t) => exprToString expr ^ ": " ^ typeAnnToString t
                        | Use (_, name) => Name.toString name
                        | Const (_, c) => Const.toString c
end