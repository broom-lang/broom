type 'a with_pos = 'a Util.with_pos

module Expr = Fc.Term.Expr
type expr = Expr.t
type pat = Expr.pat
type stmt = Fc.Term.Stmt.t

let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

module Value = struct
    type t =
        | Tuple of t Vector.t
        | Fn of ((t -> t) -> t -> t)
        | Record of t Name.Map.t
        | Proxy
        | Int of int

    let rec to_doc = function
        | Tuple vs -> PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
            PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
            to_doc (Vector.to_list vs)
        | Fn _ -> PPrint.braces (PPrint.bar ^^ PPrint.underscore ^^ PPrint.bar ^/^ PPrint.underscore)
        | Record fields ->
            let field_to_doc (label, v) =
                PPrint.infix 4 1 PPrint.equals (Name.to_doc label) (to_doc v) in
            PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                PPrint.lbrace (PPrint.comma ^^ PPrint.break 1) PPrint.rbrace
                field_to_doc (Name.Map.bindings fields)
        | Proxy -> PPrint.brackets PPrint.underscore
        | Int n -> PPrint.string (Int.to_string n)
end

module Env = struct
    module Scope = struct
        module Global = struct
            type t = Value.t Name.Hashtbl.t
            
            let create () = Name.Hashtbl.create 0
            let find = Fun.flip Name.Hashtbl.find_opt
            let add k v toplevel = Name.Hashtbl.add toplevel k v
        end

        module Local = struct
            type t = Value.t Name.Hashtbl.t

            let create () = Name.Hashtbl.create 0

            let find = Fun.flip Name.Hashtbl.find_opt

            let add k v scope = match Name.Hashtbl.find_opt scope k with
                | Some _ -> failwith "compiler bug: double definition"
                | None -> Name.Hashtbl.add scope k v
        end
    end

    type t = {global : Scope.Global.t option; locals : Scope.Local.t list}

    let interactive () = {global = Some (Scope.Global.create ()); locals = []}
    let eval () = {global = None; locals = []}

    let find {global; locals} name = match List.find_map (Scope.Local.find name) locals with
        | Some v -> v
        | None -> (match Option.bind global (Scope.Global.find name) with
            | Some v -> v
            | None -> failwith "compiler bug: unbound variable at runtime")

    let push env = {env with locals = Scope.Local.create () :: env.locals}

    let add {global; locals} k v = match locals with
        | scope :: _ -> Scope.Local.add k v scope
        | [] -> (match global with
            | Some toplevel -> Scope.Global.add k v toplevel
            | None -> failwith "compiler bug: tried to set unbound variable at runtime")
end

module Error = struct
    type t = |

    let to_doc _ = failwith "unreachable"
end

exception RuntimeException of Error.t

let match_failure () = failwith "compiler bug: pattern matching failed at runtime"

(* The interpreter is written in CPS because control effects need first-class continuations: *)

type cont = Value.t -> Value.t

type cont' = unit -> Value.t

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

    | Fn (_, {name; typ = _}, body) ->
        k (Fn (fun k v ->
            let env = Env.push env in
            Env.add env name v;
            eval env k body))

    | App (callee, _, arg) ->
        let apply f v = f k v in
        let eval_arg : cont = function
            | Fn f -> eval env (apply f) arg
            | _ -> failwith "compiler bug: tried to call non-fn at runtime" in
        eval env eval_arg callee

    | PrimApp (op, _, arg) ->
        let apply_primop (arg : Value.t) = match op with
            | IAdd | ISub | IMul -> (match arg with
                | Tuple args when Vector.length args = 2 ->
                    (match (Vector.get args 0, Vector.get args 1) with
                    | (Int a, Int b) -> k (Int (match op with
                        | IAdd -> a + b
                        | ISub -> a - b
                        | IMul -> a * b
                        | _ -> failwith "unreachable"))
                    | _ -> failwith "compiler bug: invalid primop args")
                | _ -> failwith "compiler bug: invalid primop arg")
            | Int | Type -> k Proxy in
        eval env apply_primop arg

    | Match (expr, clauses) -> (match Vector.length clauses with
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
            eval env (eval_clause 0) expr)

    | Let ((_, pat, expr), body) ->
        let k v = 
            let env = Env.push env in
            bind env (fun () -> eval env k body) match_failure pat v in
        eval env k expr

    | Letrec (defs, body) ->
        let env = Env.push env in
        let rec define i () =
            if i < Vector1.length defs then begin
                let (_, pat, expr) = Vector1.get defs i in
                let k v = bind env (define (i + 1)) match_failure pat v in
                eval env k expr
            end else eval env k body in
        define 0 ()

    | Unpack (_, {name; typ = _}, expr, body) ->
        let k v =
            let env = Env.push env in
            eval env k body in
        eval env k expr

    | LetType (_, expr) | Axiom (_, expr) | Cast (expr, _) | Pack (_, expr) -> eval env k expr
    | Use name -> k (Env.find env name)

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
                end else failwith "compiler bug: duplicate record fields" in
            let (label, expr) = Vector.get fields 0 in
            eval env (eval_fields 0 Name.Map.empty label) expr)

    | Where (base, fields) ->
        let len = Vector1.length fields in
        let rec eval_fields i base label v =
            if Name.Map.mem label base then begin
                let i = i + 1 in
                let base = Name.Map.add label v base in
                if i < len then begin
                    let (label, expr) = Vector1.get fields i in
                    eval env (eval_fields i base label) expr
                end else k (Record base)
            end else failwith "compiler bug: `where` a new label" in
        let k : cont = function
            | Record base ->
                let (label, expr) = Vector1.get fields 0 in
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

    | Select (expr, label) ->
        let k : cont = function
            | Record fields -> (match Name.Map.find_opt label fields with
                | Some v -> k v
                | None -> failwith "compiler bug: field not found")
            | _ -> failwith "compiler bug: tried to select from non-record at runtime" in
        eval env k expr

    | Proxy _ -> k Proxy
    | Const (Int n) -> k (Value.Int n)

    | Patchable eref -> TxRef.(eval env k !eref)

and bind : Env.t -> cont' -> cont' -> pat with_pos -> cont
= fun env then_k else_k pat v -> match pat.v with
    | ValuesP pats -> (match v with
        | Tuple vs when Vector.length vs = Vector.length pats -> (match Vector.length pats with
            | 0 -> then_k ()
            | len ->
                let rec bind_pats i () =
                    let i = i + 1 in
                    if i < len
                    then bind env (bind_pats i) else_k (Vector.get pats i) (Vector.get vs i)
                    else then_k () in
                bind env (bind_pats 0) else_k (Vector.get pats 0) (Vector.get vs 0))
        | _ -> else_k ())

    | UseP name -> Env.add env name v; then_k ()
    | ProxyP _ -> (match v with
        | Proxy -> then_k ()
        | _ -> else_k ())

    | ConstP (Int n) -> (match v with
        | Int n' when n' = n -> then_k ()
        | _ -> else_k ())

and exec : Env.t -> cont' -> stmt -> Value.t
= fun env k -> function
    | Def (_, pat, expr) -> eval env (bind env k match_failure pat) expr
    | Expr expr ->
        let k : cont = function
            | Tuple vs when Vector.length vs = 0 -> k ()
            | _ -> failwith "compiler bug: expr-stmt produced non-()" in
        eval env k expr

(* # Public API Functions *)

let interpret env expr =
    try Ok (eval env exit expr)
    with RuntimeException err -> Error err

let run env (stmt : stmt) =
    try match stmt with
        | Def (_, pat, expr) ->
            let res = ref None in
            let k v =
                res := Some v;
                bind env (fun () -> Option.get !res) match_failure pat v in
            Ok (eval env k expr)
        | Expr expr -> Ok (eval env exit expr)
    with RuntimeException err -> Error err

