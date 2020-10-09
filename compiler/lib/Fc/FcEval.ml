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
            let copy = Name.Hashtbl.copy
            let find = Fun.flip Name.Hashtbl.find_opt
            let add k v toplevel = Name.Hashtbl.add toplevel k v
        end

        module Local = struct
            type t = Value.t Name.Hashtbl.t

            let create () = Name.Hashtbl.create 0
            let copy = Name.Hashtbl.copy
            let find = Fun.flip Name.Hashtbl.find_opt

            let add k v scope = match Name.Hashtbl.find_opt scope k with
                | Some _ -> failwith "compiler bug: double definition"
                | None -> Name.Hashtbl.add scope k v
        end
    end

    type t = {global : Scope.Global.t option; locals : Scope.Local.t list}

    let interactive () = {global = Some (Scope.Global.create ()); locals = []}
    let eval () = interactive () (* HACK? *)

    let copy {global; locals} =
        { global = Option.map Scope.Global.copy global
        ; locals = List.map Scope.Local.copy locals }

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

let rec eval : Env.t -> cont -> expr -> Value.t
= fun env k expr -> match expr.term with
    | Values exprs -> (match Array.length exprs with
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

    | Let {def = (_, {name; _}, vexpr); body} ->
        let k v = 
            let env = Env.push env in
            Env.add env name v;
            eval env k body in
        eval env k vexpr

    | Letrec {defs; body} ->
        let env = Env.push env in
        let rec define i =
            if i < Vector1.length defs then begin
                let (_, {Expr.name; _}, vexpr) = Vector1.get defs i in
                let k v =
                    Env.add env name v;
                    define (i + 1) in
                eval env k vexpr
            end else eval env k body in
        define 0

    | Unpack {existentials = _; var = {name; _}; value = vexpr; body} ->
        let k v =
            let env = Env.push env in
            eval env k body in
        eval env k vexpr

    | LetType {body = expr; _} | Axiom {body = expr; _}
    | Cast {castee = expr; _} | Pack {impl = expr; _} -> eval env k expr
    | Use {var = {name; _}; _} -> k (Env.find env name)

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

    | Select {selectee; label} ->
        let k : cont = function
            | Record fields -> (match Name.Map.find_opt label fields with
                | Some v -> k v
                | None -> failwith "compiler bug: field not found")
            | _ -> failwith "compiler bug: tried to select from non-record at runtime" in
        eval env k selectee

    | Proxy _ -> k Proxy
    | Const (Int n) -> k (Value.Int n)

    | Patchable eref -> TxRef.(eval env k !eref)

and bind : Env.t -> cont' -> cont' -> pat -> cont
= fun env then_k else_k pat v -> match pat.pterm with
    | VarP {name; _} -> Env.add env name v; then_k ()
    | WildP -> then_k ()
    | ConstP (Int n) -> (match v with
        | Int n' when n' = n -> then_k ()
        | _ -> else_k ())

(* # Public API Functions *)

let interpret env expr =
    try Ok (eval env exit expr)
    with RuntimeException err -> Error err

let run env (stmt : stmt) =
    let env = Env.copy env in
    try match stmt with
        | Def (_, {name; _}, expr) ->
            let k v = Env.add env name v; v in
            Ok (eval env k expr, env)
        | Expr expr -> Ok (eval env exit expr, env)
    with RuntimeException err -> Error err

