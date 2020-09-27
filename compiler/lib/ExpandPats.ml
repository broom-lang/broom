open Streaming

module Expr = Fc.Term.Expr
type 'a wrapped = 'a Expr.wrapped
type stmt = Fc.Term.Stmt.t

let rec expand_clauses clauses =
    let (pats, bodies) =
        Stream.from (Vector.to_source clauses)
        |> Stream.into (Sink.zip
            (Sink.premap (fun {Expr.pat; body = _} -> pat) (Vector.sink ()))
            (Sink.premap (fun {Expr.pat = _; body} -> expand body) (Vector.sink ()))) in
    Vector.map2 (fun pat body -> {Expr.pat; body}) pats bodies (* FIXME *)

and expand : Expr.t wrapped -> Expr.t wrapped
= fun expr -> match expr.term with
    | Values _ | Focus _ | Fn _ | App _ | PrimApp _
    | LetType _ | Axiom _ | Cast _ | Pack _ | Unpack _
    | Record _ | With _ | Where _ | Select _ | Proxy _ | Patchable _ ->
        Expr.map_children expand expr
    | Match (matchee, clauses) ->
        let matchee = expand matchee in
        {expr with term = Match (matchee, expand_clauses clauses)} (* FIXME *)
    | Use _ | Const _ -> expr

let expand_stmt : stmt -> stmt = function
    | Expr expr -> Expr (expand expr)

