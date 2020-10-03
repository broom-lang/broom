open Streaming

module T = Fc.Type
module E = Fc.Term.Expr
type 'a wrapped = 'a E.wrapped
type expr = E.t
type pat = E.pat
type clause = E.clause
type stmt = Fc.Term.Stmt.t
type def = Fc.Term.Stmt.def

(* TODO: Integrate into typechecker (because of lacks constraints, later also GADTs) *)
(* TODO: Don't even need nested patterns in Fc since this unnests them immediately (?) *)

module State = struct
    type node =
        | Test of {matchee : E.lvalue; clauses : (pat wrapped * Name.t) Vector.t}
        | Destructure of {defs : def Vector.t; body : Name.t}
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

module IntMap = Map.Make(Int)

let split_int : pat wrapped Matrix.t -> int -> IntSet.t IntMap.t * IntSet.t
= fun pats col ->
    let add_single singles n i = singles |> IntMap.update n (function
        | Some branch -> Some (IntSet.add i branch)
        | None -> Some (IntSet.singleton i)) in
    let step (singles, defaults) (i, (pat : pat wrapped)) = match pat.term with
        | ConstP (Int n) -> (add_single singles n i, defaults)
        | UseP _ -> (singles, IntSet.add i defaults)
        | ValuesP _ | ProxyP _ -> failwith "unreachable" in
    let (singles, defaults) =
        Stream.from (Source.zip (Source.count 0) (Option.get (Matrix.col col pats)))
        |> Stream.into (Sink.fold step (IntMap.empty, IntSet.empty)) in
    (IntMap.map (IntSet.union defaults) singles, defaults)

let split_tuple pats coli width =
    let subpats (pat : pat wrapped) = match pat.term with
        | ValuesP pats -> pats
        | UseP _ -> Vector.init width (fun _ ->
            {pat with term = E.UseP (Name.freshen (Name.of_string "_"))})
        | ProxyP _ | ConstP _ -> failwith "unreachable" in
    let cols' = Stream.from (Option.get (Matrix.col coli pats))
        |> Stream.map subpats
        |> Matrix.of_rows in
    Matrix.hcat [Matrix.sub_cols 0 (Some coli) pats; cols'; Matrix.sub_cols (coli + 1) None pats]

let is_nontrivial : pat wrapped -> bool = fun pat -> match pat.term with
    | UseP _ | ProxyP _ -> false
    | ValuesP _ | ConstP _ -> true

let rec matcher' : Util.span -> Automaton.t -> E.lvalue Vector.t -> pat wrapped Matrix.t -> State.t Vector.t -> Name.t
= fun pos states matchees pats acceptors ->
    match Matrix.row 0 pats with
    | Some row ->
        (match Stream.from (Source.zip (Source.count 0) (Source.filter is_nontrivial row))
            |> Stream.into Sink.first with
        | Some (coli, _) -> (match (Vector.get matchees coli).typ with (* TODO: eval typ *)
            | Prim Int ->
                let (rows, default_rowis) = split_int pats coli in
                let matchee = Vector.get matchees coli in
                let matchees' = Vector.remove matchees coli in
                let pats = Matrix.remove_col coli pats in
                let clause (pat, rowis) =
                    let pats = Matrix.select_rows rowis pats in
                    let acceptors = Vector.select acceptors rowis in
                    (pat, matcher' pos states matchees' pats acceptors) in
                let clauses = Stream.concat
                    (Stream.from (Source.seq (IntMap.to_seq rows))
                        |> Stream.map (fun (n, rowis) ->
                            ( {E.term = E.ConstP (Int n); typ = matchee.typ; pos}
                            , rowis )))
                    (Stream.single ( { E.term = E.UseP (Name.freshen (Name.of_string "_"))
                                     ; typ = matchee.typ; pos}
                                   , default_rowis))
                |> Stream.map clause
                |> Stream.into (Vector.sink ()) in
                let name = Name.fresh () in
                let node : State.node = Test {matchee; clauses} in
                Automaton.add states name {name; refcount = 1; frees = Some matchees; node};
                name

            | Values typs ->
                let width = Vector.length typs in
                let pats = split_tuple pats coli width in
                let matchee = Vector.get matchees coli in
                let matchees'' = Vector.init width (fun i ->
                    {E.name = Name.fresh (); typ = Vector.get typs i}) in
                let matchees' = Vector.concat [Vector.sub matchees 0 coli; matchees''
                    ; Vector.sub matchees (coli + 1) (Vector.length matchees - (coli + 1))] in
                let defs = Stream.from (Source.zip_with (fun (matchee' : E.lvalue) i ->
                            let def = {E.term = E.UseP matchee'.name; typ = matchee'.typ; pos} in
                            ( pos, def
                            , {E.term = E.Focus ({def with term = Use matchee.name}, i); typ = matchee'.typ; pos} ))
                        (Vector.to_source matchees'')
                        (Source.count 0))
                    |> Stream.into (Vector.sink ()) in
                let body = matcher' pos states matchees' pats acceptors in
                let name = Name.fresh () in
                let node : State.node = Destructure {defs; body} in
                Automaton.add states name {name; refcount = 1; frees = Some matchees; node};
                name)

        | None ->
            let acceptor = Vector.get acceptors 0 in
            acceptor.refcount <- acceptor.refcount + 1;
            acceptor.frees <- Some matchees;
            (match acceptor.node with
            | Final {index; body} ->
                let defs = Stream.from (Source.zip_with (fun (pat : pat wrapped) (matchee : E.lvalue) ->
                    (pat.pos, pat, {E.term = E.Use matchee.name; typ = matchee.typ; pos = pat.pos})
                    ) (Source.filter (function {E.term = E.UseP _; _} -> true | _ -> false) row)
                        (Vector.to_source matchees))
                    |> Stream.into (Vector.sink ()) in
                (match Vector1.of_vector defs with
                | Some defs ->
                    Automaton.add states acceptor.name { acceptor with node =
                        Final {index; body = {body with term = Letrec (defs, body)}} }
                | None -> ())
            | _ -> failwith "unreachable");
            acceptor.name)

    | None -> failwith "nonexhaustive matching"

let matcher : Util.span -> E.lvalue -> clause Vector.t -> Automaton.t * Name.t
= fun pos matchee clauses ->
    let states = Automaton.create (Vector.length clauses) in
    let matchees = Vector.singleton matchee in
    let pats = Matrix.of_col (Vector.map (fun {E.pat; body = _} -> pat) clauses) in
    let acceptors = Vector.mapi (fun index {E.pat = _; body} ->
        let name = Name.fresh () in
        let state = {State.name; refcount = 0; frees = None; node = Final {index; body}} in
        Automaton.add states name state;
        state
    ) clauses in
    (states, matcher' pos states matchees pats acceptors)

let rec emit' : Util.span -> T.t -> Automaton.t -> E.def CCVector.vector -> Name.t -> expr wrapped
= fun pos codomain states shareds state_name ->
    let {State.name = _; refcount; frees; node} = Automaton.find states state_name in
    let expr : expr wrapped = match node with
        | Test {matchee; clauses} ->
            { term = Match ({term = Use matchee.name; typ = matchee.typ; pos},
                clauses |> Vector.map (fun (pat, target) ->
                    {E.pat; body = emit' pos codomain states shareds target}))
            ; typ = codomain; pos }
        | Destructure {defs; body} ->
            { term = E.letrec defs (emit' pos codomain states shareds body)
            ; typ = codomain; pos }
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
            ; codomain } in
        let def : pat wrapped = {term = UseP state_name; typ = ftyp; pos} in
        let params = failwith "TODO" in
        let f : expr wrapped = {term = Fn (Vector.empty, params, expr); typ = ftyp; pos} in
        CCVector.push shareds (expr.pos, def, f);
        let args = Vector.map (fun {E.name; typ} -> {E.term = E.Use name; typ; pos}) frees in
        { term = App ( {term = Use state_name; typ = ftyp; pos}, Vector.empty
            , {term = Values args; typ = domain; pos} )
        ; typ = codomain; pos}
    end

let emit : Util.span -> T.t -> Automaton.t -> Name.t -> expr wrapped
= fun pos codomain states start ->
    let shareds = CCVector.create () in
    let body = emit' pos codomain states shareds start in
    (* TODO: Warnings for redundant states (refcount = 0) *)
    match Vector1.of_vector (Vector.build shareds) with
    | Some shareds -> {term = Letrec (shareds, body); typ = codomain; pos}
    | None -> body

let expand_clauses : Util.span -> T.t -> expr wrapped -> clause Vector.t -> expr
= fun pos codomain matchee clauses ->
    let matchee_name = Name.fresh () in
    let (states, start) = matcher pos {E.name = matchee_name; typ = matchee.typ} clauses in
    let body = emit pos codomain states start in
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

