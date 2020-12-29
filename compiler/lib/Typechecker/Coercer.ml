module Expr = Fc.Term.Expr

type t = Expr.t -> Expr.t

let id = Fun.id

let coercer = Fun.id

let apply f (expr : Expr.t) = match expr.term with
    | Use _ | Const _ -> f expr
    | _ ->
        let {Expr.term = _; pos; typ; parent = _} = expr in
        let var = Expr.fresh_var typ in
        let body = f (Expr.at pos typ (Expr.use var)) in
        Expr.at pos typ (Expr.let' [|Def (pos, var, expr)|] body)

