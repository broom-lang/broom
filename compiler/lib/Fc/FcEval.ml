module Expr = Fc.Term.Expr
module Stmt = Fc.Term.Stmt
type expr = Expr.t
type pat = Expr.pat

module Value = struct
    type t =
        | Tuple of t Vector.t
        | Fn of ((t -> t) -> t -> t)
        | Record of t Name.Map.t
        | Proxy
        | Cell of t option ref
        | Int of int
        | Bool of bool
        | String of string

    let rec to_doc =
        let open PPrint in
        function
        | Tuple vs -> surround_separate_map 4 0 (parens empty)
            lparen (comma ^^ break 1) rparen
            to_doc (Vector.to_list vs)
        | Fn _ -> braces (bar ^^ blank 1 ^^ infix 4 1 (string "->") underscore underscore)
        | Record fields ->
            let field_to_doc (label, v) =
                infix 4 1 equals (Name.to_doc label) (to_doc v) in
            surround_separate_map 4 0 (braces empty)
                lbrace (comma ^^ break 1) rbrace
                field_to_doc (Name.Map.bindings fields)
        | Proxy -> brackets underscore
        | Cell v -> sharp ^^ angles (string "cell" ^/^ match !v with
            | Some contents -> to_doc contents
            | None -> string "uninitialized")
        | Int n -> string (Int.to_string n)
        | Bool true -> string "True"
        | Bool false -> string "False"
        | String s -> dquotes (string s)
end

module Namespace = struct
    module Map = Name.Hashtbl

    type t = Value.t Map.t

    let create () = Map.create 0
    let add = Map.add
    let find = Map.find
    let clone = Map.copy
end

module Env = struct
    module Scope = struct
        type t = Value.t Name.Hashtbl.t

        let create () = Name.Hashtbl.create 0
        let find = Fun.flip Name.Hashtbl.find_opt

        let add k v scope = match Name.Hashtbl.find_opt scope k with
            | Some _ -> failwith "compiler bug: double definition"
            | None -> Name.Hashtbl.add scope k v
    end

    type t = Scope.t list

    let empty = []

    let find env name = match List.find_map (Scope.find name) env with
        | Some v -> v
        | None -> failwith "compiler bug: unbound variable at runtime"

    let push env = Scope.create () :: env

    let add env k v = match env with
        | scope :: _ -> Scope.add k v scope
        | [] -> failwith "compiler bug: tried to set unbound variable at runtime"
end

let match_failure () = failwith "compiler bug: pattern matching failed at runtime"

(* The interpreter is written in CPS because control effects need first-class continuations: *)

type cont = Value.t -> Value.t

type cont' = unit -> Value.t

let exit = Fun.id

let run (ns : Namespace.t) program =
    let ns = Namespace.clone ns in

    let rec eval : Env.t -> cont -> expr -> Value.t
    = fun env k expr -> match expr.term with
        | Tuple exprs -> (match Array.length exprs with
            | 0 -> k (Tuple Vector.empty)
            | len ->
                let rec eval_values i vs v =
                    let i = i + 1 in
                    let vals = Vector.append vs (Vector.singleton v) in
                    if i < len
                    then eval env (eval_values i vals) (Array.get exprs i)
                    else k (Tuple vals) in
                eval env (eval_values 0 Vector.empty) (Array.get exprs 0))

        | Focus {focusee; index} ->
            let k : cont = function
                | Tuple vs when index < Vector.length vs -> k (Vector.get vs index)
                | Tuple _ -> failwith "compiler bug: tuple index out of bounds"
                | _ -> failwith "compiler bug: tuple-indexing non-tuple at runtime" in
            eval env k focusee

        | Fn {universals = _; param = {name; _}; body} ->
            k (Fn (fun k v ->
                let env = Env.push env in
                Env.add env name v;
                eval env k body))

        | App {callee; universals = _; arg} ->
            let apply f v = f k v in
            let eval_arg : cont = function
                | Fn f -> eval env (apply f) arg
                | _ -> failwith "compiler bug: tried to call non-fn at runtime" in
            eval env eval_arg callee

        | PrimApp {op; universals = _; arg} ->
            let apply_op (arg : Value.t) : Value.t = match op with
                | CellNew -> k (Cell (ref None))
                | CellInit -> (match arg with
                    | Tuple args when Vector.length args = 2 ->
                        (match (Vector.get args 0, Vector.get args 1) with
                        | (Cell cell, v) -> (match !cell with
                            | None -> cell := Some v; k (Tuple Vector.empty)
                            | Some _ ->
                                failwith "compiler bug: cellInit on initialized cell at runtime")
                        | _ -> failwith "compiler bug: cellInit on non-cell at runtime")
                    | _ -> failwith "compiler bug: invalid primop arg")
                | CellGet -> (match arg with
                    | Tuple args when Vector.length args = 1 ->
                        (match Vector.get args 0 with
                        | Cell cell -> (match !cell with
                            | Some v -> k v
                            | None ->
                                failwith "compiler bug: cellGet on uninitialized cell at runtime")
                        | _ -> failwith "compiler bug: cellGet on non-cell at runtime")
                    | _ -> failwith "compiler bug: invalid primop arg")
                | Int | String | Type | TypeOf -> k Proxy
                | GlobalSet -> (match arg with
                    | Tuple args when Vector.length args = 2 ->
                        (match Vector.get args 0 with
                        | String name ->
                            Namespace.add ns (Name.of_string name) (Vector.get args 1);
                            k (Tuple Vector.empty)
                        | _ -> failwith "compiler bug: globalSet name not a string at runtime")
                    | _ -> failwith "compiler bug: invalid primop arg")
                | GlobalGet -> (match arg with
                    | Tuple args when Vector.length args = 1 ->
                        (match Vector.get args 0 with
                        | String name -> k (Namespace.find ns (Name.of_string name))
                        | _ -> failwith "compiler bug: globalGet name not a string at runtime")
                    | _ -> failwith "compiler bug: invalid primop arg")
                | Import -> failwith "TODO: foreign import in interpreter" in
            eval env apply_op arg

        | PrimBranch {op; universals = _; arg; clauses = _} -> (* FIXME: use `clauses` *)
            let apply_op (arg : Value.t) = match op with
                | IAdd | ISub | IMul | IDiv -> (match arg with
                    | Tuple args when Vector.length args = 2 ->
                        (match (Vector.get args 0, Vector.get args 1) with
                        | (Int a, Int b) -> k (Int (match op with
                            | IAdd -> a + b
                            | ISub -> a - b
                            | IMul -> a * b
                            | IDiv -> a / b
                            | _ -> failwith "unreachable"))
                        | _ -> failwith "compiler bug: invalid primop args")
                    | _ -> failwith "compiler bug: invalid primop arg")
                | ILt | ILe | IGt | IGe | IEq -> (match arg with
                    | Tuple args when Vector.length args = 2 ->
                        (match (Vector.get args 0, Vector.get args 1) with
                        | (Int a, Int b) -> k (Bool (match op with
                            | ILt -> a < b
                            | ILe -> a <= b
                            | IGt -> a > b
                            | IGe -> a >= b
                            | IEq -> Int.equal a b
                            | _ -> failwith "unreachable"))
                        | _ -> failwith "compiler bug: invalid primop args")
                    | _ -> failwith "compiler bug: invalid primop arg") in
            eval env apply_op arg

        | Match {matchee; clauses} -> (match Vector.length clauses with
            | 0 -> match_failure ()
            | len ->
                let rec eval_clause i v =
                    if i < len then begin
                        let {Expr.pat; body} = Vector.get clauses i in
                        let env = Env.push env in
                        bind env
                            (fun () -> eval env k body)
                            (fun () -> eval_clause (i + 1) v)
                            pat v
                    end else match_failure () in
                eval env (eval_clause 0) matchee)

        | Unpack {existentials = _; var = {name; _}; value = vexpr; body} ->
            let k v = 
                let env = Env.push env in
                Env.add env name v;
                eval env k body in
            eval env k vexpr

        | Let {defs; body} ->
            let env = Env.push env in
            let rec define i =
                if i < Array1.length defs then match Array1.get defs i with
                    | Def (_, {Expr.name; _}, vexpr) ->
                        let k v =
                            Env.add env name v;
                            define (i + 1) in
                        eval env k vexpr
                    | Expr expr ->
                        let k _ = define (i + 1) in
                        eval env k expr
                else eval env k body in
            define 0

        | LetType {body = expr; _} | Axiom {body = expr; _}
        | Cast {castee = expr; _} | Pack {impl = expr; _} -> eval env k expr

        | Use {name; _} -> k (Env.find env name)

        | Record fields -> (match Array.length fields with
            | 0 -> k (Record Name.Map.empty)
            | len ->
                let rec eval_fields i r label v =
                    if not (Name.Map.mem label r) then begin
                        let i = i + 1 in
                        let r = Name.Map.add label v r in
                        if i < len then begin
                            let (label, expr) = Array.get fields i in
                            eval env (eval_fields i r label) expr
                        end else k (Record r)
                    end else failwith "compiler bug: duplicate record fields" in
                let (label, expr) = Array.get fields 0 in
                eval env (eval_fields 0 Name.Map.empty label) expr)

        | Where {base; fields} ->
            let len = Array1.length fields in
            let rec eval_fields i base label v =
                if Name.Map.mem label base then begin
                    let i = i + 1 in
                    let base = Name.Map.add label v base in
                    if i < len then begin
                        let (label, expr) = Array1.get fields i in
                        eval env (eval_fields i base label) expr
                    end else k (Record base)
                end else failwith "compiler bug: `where` a new label" in
            let k : cont = function
                | Record base ->
                    let (label, expr) = Array1.get fields 0 in
                    eval env (eval_fields 0 base label) expr
                | _ -> failwith "compiler bug: `where` to a non-record" in
            eval env k base

        | With {base; label; field} ->
            let k : cont = function
                | Record fields when not (Name.Map.mem label fields) ->
                    let k fv = k (Record (Name.Map.add label fv fields)) in
                    eval env k field
                | Record _ -> failwith "compiler bug: `with` pre-existing field"
                |_ -> failwith "compiler bug: `with` to a non_record" in
            eval env k base

        | Select {selectee; label} ->
            let k : cont = function
                | Record fields -> (match Name.Map.find_opt label fields with
                    | Some v -> k v
                    | None -> failwith "compiler bug: field not found")
                | _ -> failwith "compiler bug: tried to select from non-record at runtime" in
            eval env k selectee

        | Proxy _ -> k Proxy
        | Const (Int n) -> k (Value.Int n)
        | Const (String s) -> k (Value.String s)

        | Patchable eref -> TxRef.(eval env k !eref)

        | Letrec _ -> failwith "compiler bug: encountered `letrec` at runtime"

    and bind : Env.t -> cont' -> cont' -> pat -> cont
    = fun env then_k else_k pat v -> match pat.pterm with
        | VarP {name; _} -> Env.add env name v; then_k ()
        | WildP _ -> then_k ()
        | ConstP (Int n) -> (match v with
            | Int n' when n' = n -> then_k ()
            | _ -> else_k ())
        | ConstP (String s) -> (match v with
            | String s' when s' = s -> then_k ()
            | _ -> else_k ())
        | TupleP _ | ProxyP _ -> failwith "unreachable" in

    let {type_fns = _; defs; main} : Fc.Program.t = program in
    let pos =
        ( (if Vector.length defs > 0
          then (let (pos, _, _) = Vector.get defs 0 in fst pos)
          else fst main.pos)
        , snd main.pos ) in
    let defs = defs |> Vector.to_array |> Array.map (fun def -> Stmt.Def def) in
    let expr = Expr.at pos main.typ (Expr.let' defs main) in
    (ns, eval Env.empty exit expr)

