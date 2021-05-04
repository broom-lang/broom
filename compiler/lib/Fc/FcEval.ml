open Asserts

module Expr = Fc.Term.Expr
module Stmt = Fc.Term.Stmt
type expr = Expr.t
type pat = Expr.pat

module Env = struct
    module Scope = struct
        type t = Value.t Name.Hashtbl.t

        let create () = Name.Hashtbl.create 0
        let find = Fun.flip Name.Hashtbl.find_opt

        let add pos k v scope = match Name.Hashtbl.find_opt scope k with
            | Some _ -> bug (Some pos) ~msg: "double definition"
            | None -> Name.Hashtbl.add scope k v
    end

    type t = Scope.t list

    let empty = []

    let find pos env name = match List.find_map (Scope.find name) env with
        | Some v -> v
        | None -> bug (Some pos) ~msg: "unbound variable at runtime"

    let push env = Scope.create () :: env

    let add pos env k v = match env with
        | scope :: _ -> Scope.add pos k v scope
        | [] -> bug (Some pos) ~msg: "tried to set unbound variable at runtime"
end

let match_failure pos = bug (Some pos) ~msg: "pattern matching failed at runtime"

(* The interpreter is written in CPS because control effects need first-class continuations: *)

type cont = Value.t -> Value.t

type cont' = unit -> Value.t

let exit = Fun.id

let run (ns : Namespace.t) program =
    let rec eval : Env.t -> cont -> expr -> Value.t
    = fun env k expr -> match expr.term with
        | Pair {fst; snd} ->
            let k fst =
                let k snd = k (Pair {fst; snd}) in
                eval env k snd in
            eval env k fst

        | Fst arg ->
            let k : cont = function
                | Pair {fst; snd = _} -> k fst
                | _ -> bug (Some expr.pos) ~msg: "fst of non-pair at runtime" in
            eval env k arg

        | Snd arg ->
            let k : cont = function
                | Pair {fst = _; snd} -> k snd
                | _ -> bug (Some expr.pos) ~msg: "fst of non-pair at runtime" in
            eval env k arg

        | Fn {universals = _; param = {name; _}; body} ->
            k (Fn (fun k v ->
                let env = Env.push env in
                Env.add expr.pos env name v;
                eval env k body))

        | App {callee; universals = _; arg} ->
            let apply f v = f k v in
            let eval_arg : cont = function
                | Fn f -> eval env (apply f) arg
                | _ -> bug (Some expr.pos) ~msg: "tried to call non-fn at runtime" in
            eval env eval_arg callee

        | PrimApp {op; universals = _; args} ->
            let apply_op (args : Value.t Vector.t) : Value.t = match op with
                | Pair ->
                    if Vector.length args = 2
                    then Pair {fst = Vector.get args 0; snd = Vector.get args 1}
                    else bug (Some expr.pos) ~msg: "invalid primop arg count"

                | Fst ->
                    if Vector.length args = 1
                    then (match Vector.get args 0 with
                        | Pair {fst; snd = _} -> k fst
                        | _ -> bug (Some expr.pos) ~msg: ".0 on non-pair at runtime")
                    else bug (Some expr.pos) ~msg: "invalid primop arg count"

                | Snd ->
                    if Vector.length args = 1
                    then (match Vector.get args 0 with
                        | Pair {fst = _; snd} -> k snd
                        | _ -> bug (Some expr.pos) ~msg: ".0 on non-pair at runtime")
                    else bug (Some expr.pos) ~msg: "invalid primop arg count"

                | CellNew -> k (Cell (ref None))

                | CellInit ->
                    if Vector.length args = 2 then
                        (match (Vector.get args 0, Vector.get args 1) with
                        | (Cell cell, v) -> (match !cell with
                            | None -> cell := Some v; k Unit
                            | Some _ ->
                                bug (Some expr.pos) ~msg: "cellInit on initialized cell at runtime")
                        | _ -> bug (Some expr.pos) ~msg: "cellInit on non-cell at runtime")
                    else bug (Some expr.pos) ~msg: "invalid primop arg count"

                | CellGet ->
                    if Vector.length args = 1 then
                        (match Vector.get args 0 with
                        | Cell cell -> (match !cell with
                            | Some v -> k v
                            | None ->
                                bug (Some expr.pos) ~msg: "cellGet on uninitialized cell at runtime")
                        | _ -> bug (Some expr.pos) ~msg: "cellGet on non-cell at runtime")
                    else bug (Some expr.pos) ~msg: "invalid primop arg count"

                | Int | String | Type | TypeOf -> k Proxy

                | GlobalSet ->
                    if Vector.length args = 2 then
                        (match Vector.get args 0 with
                        | String name ->
                            (match Option.bind (Name.parse name) (Namespace.find ns) with
                            | Some var ->
                                var := Some (Vector.get args 1);
                                k Unit
                            | None -> bug (Some expr.pos) ~msg: ("global " ^ name ^ " not found at runtime"))
                        | _ -> bug (Some expr.pos) ~msg: "globalSet name not a string at runtime")
                    else bug (Some expr.pos) ~msg: "invalid primop arg count"

                | GlobalGet ->
                    if Vector.length args = 1 then
                        (match Vector.get args 0 with
                        | String name ->
                            (match Option.bind (Name.parse name) (Namespace.find ns) with
                            | Some var ->
                                (match !var with
                                | Some v -> k v
                                | None ->
                                    bug (Some expr.pos)
                                        ~msg: ("tried to read uninitialized global " ^ name ^ " at runtime"))
                            | None -> bug (Some expr.pos) ~msg: ("global " ^ name ^ " not found at runtime"))
                        | _ -> bug (Some expr.pos) ~msg: "globalGet name not a string at runtime")
                    else bug (Some expr.pos) ~msg: "invalid primop arg count"

                | Import -> todo (Some expr.pos) ~msg: "foreign import in interpreter" in
            (match Vector.length args with
            | 0 -> apply_op Vector.empty
            | len ->
                let rec eval_args i vs v =
                    let i = i + 1 in
                    let vals = Vector.append vs (Vector.singleton v) in
                    if i < len
                    then eval env (eval_args i vals) (Vector.get args i)
                    else apply_op vals in
                eval env (eval_args 0 Vector.empty) (Vector.get args 0))

        | PrimBranch {op; universals = _; args; clauses = _} -> (* FIXME: use `clauses` *)
            let apply_op (args : Value.t Vector.t) = match op with
                | IAdd | ISub | IMul | IDiv ->
                    if Vector.length args = 2 then
                        (match (Vector.get args 0, Vector.get args 1) with
                        | (Int a, Int b) -> k (Int (match op with
                            | IAdd -> a + b
                            | ISub -> a - b
                            | IMul -> a * b
                            | IDiv -> a / b
                            | _ -> unreachable (Some expr.pos)))
                        | _ -> bug (Some expr.pos) ~msg: "invalid primop args")
                    else bug (Some expr.pos) ~msg: "invalid primop arg"

                | ILt | ILe | IGt | IGe | IEq ->
                    if Vector.length args = 2 then
                        (match (Vector.get args 0, Vector.get args 1) with
                        | (Int a, Int b) -> k (Bool (match op with
                            | ILt -> a < b
                            | ILe -> a <= b
                            | IGt -> a > b
                            | IGe -> a >= b
                            | IEq -> Int.equal a b
                            | _ -> unreachable (Some expr.pos)))
                        | _ -> bug (Some expr.pos) ~msg: "invalid primop args")
                    else bug (Some expr.pos) ~msg: "invalid primop arg" in
            (match Vector.length args with
            | 0 -> apply_op Vector.empty
            | len ->
                let rec eval_args i vs v =
                    let i = i + 1 in
                    let vals = Vector.append vs (Vector.singleton v) in
                    if i < len
                    then eval env (eval_args i vals) (Vector.get args i)
                    else apply_op vals in
                eval env (eval_args 0 Vector.empty) (Vector.get args 0))

        | Match {matchee; clauses} -> (match Vector.length clauses with
            | 0 -> match_failure expr.pos
            | len ->
                let rec eval_clause i v =
                    if i < len then begin
                        let {Expr.pat; body} = Vector.get clauses i in
                        let env = Env.push env in
                        bind env
                            (fun () -> eval env k body)
                            (fun () -> eval_clause (i + 1) v)
                            pat v
                    end else match_failure expr.pos in
                eval env (eval_clause 0) matchee)

        | Unpack {existentials = _; var = {name; _}; value = vexpr; body} ->
            let k v = 
                let env = Env.push env in
                Env.add expr.pos env name v;
                eval env k body in
            eval env k vexpr

        | Let {defs; body} ->
            let env = Env.push env in
            let rec define i =
                if i < Vector1.length defs then match Vector1.get defs i with
                    | Def (pos, pat, vexpr) -> (match pat with
                        | {pterm = VarP {name; _}; _} ->
                            let k v =
                                Env.add pos env name v;
                                define (i + 1) in
                            eval env k vexpr
                        | {ppos; _} ->
                            bug (Some ppos) ~msg: "encountered non-variable pattern at runtime")
                    | Expr expr ->
                        let k _ = define (i + 1) in
                        eval env k expr
                else eval env k body in
            define 0

        | LetType {body = expr; _} | Axiom {body = expr; _}
        | Cast {castee = expr; _} | Pack {impl = expr; _} -> eval env k expr

        | Use {name; _} -> k (Env.find expr.pos env name)

        | Record fields -> (match Vector.length fields with
            | 0 -> k (Record Name.Map.empty)
            | len ->
                let rec eval_fields i r label v =
                    if not (Name.Map.mem label r) then begin
                        let i = i + 1 in
                        let r = Name.Map.add label v r in
                        if i < len then begin
                            let (label, expr) = Vector.get fields i in
                            eval env (eval_fields i r label) expr
                        end else k (Record r)
                    end else bug (Some expr.pos) ~msg: "duplicate record fields" in
                let (label, expr) = Vector.get fields 0 in
                eval env (eval_fields 0 Name.Map.empty label) expr)

        | Where {base; fields} ->
            let len = Vector1.length fields in
            let rec eval_fields i base label v =
                if Name.Map.mem label base then begin
                    let i = i + 1 in
                    let base = Name.Map.add label v base in
                    if i < len then begin
                        let (label, expr) = Vector1.get fields i in
                        eval env (eval_fields i base label) expr
                    end else k (Record base)
                end else bug (Some expr.pos) ~msg: "`where` a new label" in
            let k : cont = function
                | Record base ->
                    let (label, expr) = Vector1.get fields 0 in
                    eval env (eval_fields 0 base label) expr
                | _ -> bug (Some expr.pos) ~msg: "`where` to a non-record" in
            eval env k base

        | With {base; label; field} ->
            let k : cont = function
                | Record fields when not (Name.Map.mem label fields) ->
                    let k fv = k (Record (Name.Map.add label fv fields)) in
                    eval env k field
                | Record _ -> bug (Some expr.pos) ~msg: "`with` pre-existing field"
                |_ -> bug (Some expr.pos) ~msg: "`with` to a non_record" in
            eval env k base

        | Select {selectee; label} ->
            let k : cont = function
                | Record fields -> (match Name.Map.find_opt label fields with
                    | Some v -> k v
                    | None -> bug (Some expr.pos) ~msg: "field not found")
                | _ -> bug (Some expr.pos) ~msg: "tried to select from non-record at runtime" in
            eval env k selectee

        | Proxy _ -> k Proxy
        | Const Unit -> k Unit
        | Const (Int n) -> k (Int n)
        | Const (String s) -> k (String s)

        | Convert _ -> bug (Some expr.pos) ~msg: "uncountered Convert expr node at runtime"
        | Letrec _ -> bug (Some expr.pos) ~msg: "encountered `letrec` at runtime"

    and bind : Env.t -> cont' -> cont' -> pat -> cont
    = fun env then_k else_k pat v -> match pat.pterm with
        | View (_, _) -> todo (Some pat.ppos)
        | VarP {name; _} -> Env.add pat.ppos env name v; then_k ()
        | WildP _ -> then_k ()

        | ConstP Unit -> (match v with
            | Unit -> then_k ()
            | _ -> else_k ())

        | ConstP (Int n) -> (match v with
            | Int n' when n' = n -> then_k ()
            | _ -> else_k ())

        | ConstP (String s) -> (match v with
            | String s' when s' = s -> then_k ()
            | _ -> else_k ())

        | PairP _ | ProxyP _ -> unreachable (Some pat.ppos) in

    let {type_fns = _; defs; main} : Fc.Program.t = program in
    let pos =
        ( (if Vector.length defs > 0
          then (let (pos, _, _) = Vector.get defs 0 in fst pos)
          else fst main.pos)
        , snd main.pos ) in
    let defs = defs |> Vector.map (fun def -> Stmt.Def def) in
    let expr = Expr.at pos main.typ (Expr.let' defs main) in
    eval Env.empty exit expr

