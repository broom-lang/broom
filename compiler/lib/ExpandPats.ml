open Streaming

module T = Fc.Type
module E = Fc.Term.Expr
type 'a wrapped = 'a E.wrapped
type expr = E.t
type pat = E.pat
type clause = E.clause
type stmt = Fc.Term.Stmt.t

(* TODO: Integrate into typechecker (because of lacks constraints, later also GADTs) *)
(* TODO: Don't even need nested patterns in Fc since this unnests them immediately (?) *)

module State = struct
    type node =
        | Test of {matchee : E.lvalue; clauses : (pat wrapped * Name.t) Vector.t}
        | Final of {index : int; body : expr wrapped}

    type t =
        { name : Name.t
        ; mutable refcount : int
        ; mutable frees : E.lvalue Vector.t option
        ; node : node }
end

module Automaton = struct
    include Name.Hashtbl
    type table = State.t t
    type t = table
end

let is_trivial : pat wrapped -> bool = fun pat -> match pat.term with
    | UseP _ | ProxyP _ -> true (* NOTE: ProxyP matches all inputs (of the correct type) *)
    | ValuesP _ | AppP _ | ConstP _ -> false

let matcher' : Automaton.t -> E.lvalue Vector.t -> pat wrapped Matrix.t -> State.t Vector.t -> Name.t
= fun states matchees pats acceptors ->
    match Matrix.row 0 pats with
    | Some pats ->
        if Stream.into (Sink.all ~where: is_trivial) (Stream.from pats) then begin
            let acceptor = Vector.get acceptors 0 in
            acceptor.refcount <- acceptor.refcount + 1;
            acceptor.frees <- Some matchees;
            (match acceptor.node with
            | Final {index; body} ->
                let defs = Stream.from (Source.zip_with (fun (pat : pat wrapped) (matchee : E.lvalue) ->
                    (pat.pos, pat, {E.term = E.Use matchee.name; typ = matchee.typ; pos = pat.pos})
                    ) pats (Vector.to_source matchees))
                    |> Stream.into (Vector.sink ()) in
                (match Vector1.of_vector defs with
                | Some defs ->
                    Automaton.add states acceptor.name { acceptor with node =
                        Final {index; body = {body with term = Letrec (defs, body)}} }
                | None -> ())
            | _ -> failwith "unreachable");
            acceptor.name
        end else failwith "TODO: mixture rule"

    | None -> failwith "nonexhaustive matching"

let matcher : E.lvalue -> clause Vector.t -> Automaton.t * Name.t
= fun matchee clauses ->
    let states = Automaton.create (Vector.length clauses) in
    let matchees = Vector.singleton matchee in
    let pats = Matrix.of_col (Vector.map (fun {E.pat; body = _} -> pat) clauses) in
    let acceptors = Vector.mapi (fun index {E.pat = _; body} ->
        let name = Name.fresh () in
        let state = {State.name; refcount = 0; frees = None; node = Final {index; body}} in
        Automaton.add states name state;
        state
    ) clauses in
    (states, matcher' states matchees pats acceptors)

let rec emit' : Util.span -> T.t -> Automaton.t -> E.def CCVector.vector -> Name.t -> expr wrapped
= fun pos typ states shareds state_name ->
    let {State.name = _; refcount; frees; node} = Automaton.find states state_name in
    let expr : expr wrapped = match node with
        | Test {matchee; clauses} ->
            { term = Match ({term = Use matchee.name; typ = matchee.typ; pos},
                clauses |> Vector.map (fun (pat, target) ->
                    {E.pat; body = emit' pos typ states shareds target}))
            ; typ; pos }
        | Final {index = _; body} -> body in
    if refcount = 1
    then expr
    else begin
        let pos = expr.pos in
        let frees = Option.get frees in
        let domain : T.t = Values (Vector.map (fun {E.name = _; typ} -> typ) frees) in
        let ftyp = T.Pi { universals = Vector.empty
            ; domain = Ior.Right { edomain = domain 
                ; eff = EmptyRow } (* NOTE: effect does not matter any more... *)
            ; codomain = typ } in
        let def : pat wrapped = {term = UseP state_name; typ = ftyp; pos} in
        let params = failwith "TODO" in
        let f : expr wrapped = {term = Fn (Vector.empty, params, expr); typ = ftyp; pos} in
        CCVector.push shareds (expr.pos, def, f);
        let args = Vector.map (fun {E.name; typ} -> {E.term = E.Use name; typ; pos}) frees in
        { term = App ( {term = Use state_name; typ = ftyp; pos}, Vector.empty
            , {term = Values args; typ = domain; pos} )
        ; typ; pos}
    end

let emit : Util.span -> T.t -> Automaton.t -> Name.t -> expr wrapped
= fun pos typ states start ->
    let shareds = CCVector.create () in
    let body = emit' pos typ states shareds start in
    (* TODO: Warnings for redundant states (refcount = 0) *)
    match Vector1.of_vector (Vector.build shareds) with
    | Some shareds -> {term = Letrec (shareds, body); typ; pos}
    | None -> body

let expand_clauses : Util.span -> T.t -> expr wrapped -> clause Vector.t -> expr
= fun pos typ matchee clauses ->
    let matchee_name = Name.fresh () in
    let (states, start) = matcher {E.name = matchee_name; typ = matchee.typ} clauses in
    let body = emit pos typ states start in
    E.Let ((pos, {term = UseP matchee_name; typ = matchee.typ; pos = matchee.pos}, matchee), body)

let rec expand : E.t wrapped -> E.t wrapped
= fun expr ->
    let expr = E.map_children expand expr in
    match expr.term with
    | Values _ | Focus _ | Fn _ | App _ | PrimApp _
    | LetType _ | Axiom _ | Cast _ | Pack _ | Unpack _
    | Record _ | With _ | Where _ | Select _ | Proxy _
    | Use _ | Const _ | Patchable _ -> expr
    | Match (matchee, clauses) -> {expr with term = expand_clauses expr.pos expr.typ matchee clauses}

let expand_stmt : stmt -> stmt = function
    | Expr expr -> Expr (expand expr)

