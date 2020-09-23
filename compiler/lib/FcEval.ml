type 'a with_pos = 'a Util.with_pos
type expr = Fc.Term.Expr.t
type pat = Fc.Term.Expr.pat
type stmt = Fc.Term.Stmt.t

let (^^) = PPrint.(^^)

module Value = struct
    type t =
        | Tuple of t Vector.t
        | Int of int

    let rec to_doc = function
        | Int n -> PPrint.string (Int.to_string n)
        | Tuple vs -> PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
            PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
            to_doc (Vector.to_list vs)
end

module Env = struct
    type t = Value.t Name.Map.t

    let interactive () = Name.Map.empty
    let eval () = Name.Map.empty
end

module Error = struct
    type t = |

    let to_doc _ = failwith "unreachable"
end

exception RuntimeException of Error.t

let match_failure _ = failwith "compiler bug: pattern matching failed at runtime"

type cont = Value.t -> Value.t

let exit = Fun.id

let rec eval : Env.t -> cont -> expr with_pos -> Value.t
= fun env k expr -> match expr.v with
    | Values exprs -> (match Vector.length exprs with
        | 0 -> k (Tuple Vector.empty)
        | len ->
            let rec eval_values i vs v =
                let i = i + 1 in
                let vals = Vector.append vs (Vector.singleton v) in
                if i < len
                then eval env (eval_values i vals) (Vector.get exprs i)
                else k (Tuple vals) in
            eval env (eval_values 0 Vector.empty) (Vector.get exprs 0))
    | Focus (expr, i) ->
        let k : cont = function
            | Tuple vs when i < Vector.length vs -> k (Vector.get vs i)
            | Tuple _ -> failwith "compiler bug: tuple index out of bounds"
            | _ -> failwith "compiler bug: tuple-indexing non-tuple at runtime" in
        eval env k expr
    | Pack (_, expr) -> eval env k expr
    | Const (Int n) -> k (Value.Int n)

and bind : Env.t -> cont -> cont -> pat with_pos -> cont
= fun env then_k else_k pat v -> match pat.v with
    | ConstP (Int n) -> (match v with
        | Int n' ->
            if n' = n
            then then_k (Tuple Vector.empty) (* NOTE: Arbitrarily, will be discarded anyway *)
            else else_k v)

and exec : Env.t -> cont -> stmt -> Value.t
= fun env k -> function
    | Def (_, pat, expr) -> eval env (bind env k match_failure pat) expr
    | Expr expr -> eval env k expr

let interpret env expr =
    try
        Ok (eval env exit expr)
    with RuntimeException err -> Error err

let run env stmt =
    try
        Ok (exec env exit stmt)
    with RuntimeException err -> Error err

