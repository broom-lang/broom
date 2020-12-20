open Streaming

module T = Fc.Type
module E = Fc.Term.Expr
module S = Fc.Term.Stmt
type var = E.var
type expr = E.t
type pat = E.pat
type stmt = Fc.Term.Stmt.t

type ctx = Inline | Shared of var | Redirect of var
type final_naming = {tmp_var : var; src_var : var}
type final_emitter = ctx -> final_naming Vector.t -> E.t
type clause' = {pat : pat; emit : final_emitter}

(* TODO: `let {(x, y) = ...; ...}` should produce
    `let t#42 = ...; x = t#42.0; y = t#42.1; in ...` or at least
    `let t#42 = ...; x#43 = t#42.0; y#44 = t#42.1; x = x#43; y = y#44; in ...`  instead of the silly
    `let
        t#45 = let t#42 = ...; x#43 = t#42.0; y#44 = t#42.1; in (x#43, y#44) end
        x = t#45.0; y = t#45.1;
     in ...`
     Flattening `let x = let y = ...; z = ...; in ...;` into
     `let y = ...; z = ...; x = ...;` and eliding the final tuple when pattern was purely
     destructuring (i.e. no or patterns, so no `match`es are generated) should suffice as MVP. *)
(* TODO: Also deduplicate internal nodes as in Pettersson paper *)
(* TODO: Don't even need nested patterns in Fc since this unnests them immediately (?) *)

module State = struct
    type node =
        | Test of {matchee : var; clauses : (pat * var) Vector.t}
        | Destructure of {defs : stmt Vector.t; body : var}
        | Final of {mutable tmp_vars : final_naming Vector.t option; emit : final_emitter}

    type t =
        { var : var
        ; mutable refcount : int
        ; mutable frees : var Vector.t option
        ; node : node }
end

module Automaton = struct
    include Name.Hashtbl
end

module IntMap = Map.Make(Int)

let split_int : pat Matrix.t -> int -> pat Matrix.t * IntSet.t IntMap.t * IntSet.t
= fun pats col ->
    let new_pat (pat : pat) = match pat.pterm with
        | ConstP (Int _) -> {pat with pterm = WildP (Name.of_string "")}
        | _ -> pat in
    let add_single singles n i = singles |> IntMap.update n (function
        | Some branch -> Some (IntSet.add i branch)
        | None -> Some (IntSet.singleton i)) in
    let step (singles, defaults) (i, (pat : pat)) = match pat.pterm with
        | ConstP (Int n) -> (add_single singles n i, defaults)
        | VarP _ | WildP _ -> (singles, IntSet.add i defaults)
        | ConstP _ | TupleP _ | ProxyP _ -> failwith "unreachable" in
    let (col', (singles, defaults)) =
        Stream.from (Source.zip (Source.count 0) (Option.get (Matrix.col col pats)))
        |> Stream.into (Sink.zip
            (Vector.sink ()
            |> Sink.premap (fun (_, pat) -> new_pat pat))
            (Sink.fold step (IntMap.empty, IntSet.empty))) in
    ( Matrix.hcat [Matrix.sub_cols 0 (Some col) pats; Matrix.of_col col'
        ; Matrix.sub_cols (col + 1) None pats]
    , IntMap.map (IntSet.union defaults) singles, defaults )

let split_tuple pats coli width =
    let subpats (pat : pat) = match pat.pterm with
        | TupleP pats -> pats
        | VarP _ | WildP _ -> Vector.init width (fun _ -> {pat with pterm = WildP (Name.of_string "")})
        | ProxyP _ | ConstP _ -> failwith "unreachable" in
    let cols' = Stream.from (Option.get (Matrix.col coli pats))
        |> Stream.map subpats
        |> Matrix.of_rows in
    Matrix.hcat [Matrix.sub_cols 0 (Some coli) pats; cols'; Matrix.sub_cols (coli + 1) None pats]

let is_trivial : pat -> bool = fun pat -> match pat.pterm with
    | VarP _ | WildP _ | ProxyP _ -> true
    | TupleP _ | ConstP _ -> false

let is_named (pat : pat) = match pat.pterm with
    | VarP _ -> true
    | _ -> false

let matcher pos typ matchee clauses =
    let states = Automaton.create (Vector.length clauses) in

    let rec matcher' (matchees : var Vector.t) pats acceptors =
        match Matrix.row 0 pats with
        | Some row ->
            let coli = Stream.from row
                |> Stream.take_while is_trivial
                |> Stream.into Sink.len in

            if coli < Vector.length matchees then
                (match (Vector.get matchees coli).vtyp with (* TODO: eval typ *)
                | Prim Int ->
                    let (pats, rows, default_rowis) = split_int pats coli in
                    let matchee = Vector.get matchees coli in
                    let clause (pat, rowis) =
                        let pats = Matrix.select_rows rowis pats in
                        let acceptors = Vector.select acceptors rowis in
                        (pat, matcher' matchees pats acceptors) in
                    let clauses = Stream.concat
                            (Stream.from (Source.seq (IntMap.to_seq rows))
                                |> Stream.map (fun (n, rowis) ->
                                    ( {E.pterm = E.ConstP (Int n); ptyp = matchee.vtyp; ppos = pos}
                                    , rowis )))
                            (Stream.single ( {E.pterm = WildP (Name.of_string ""); ptyp = matchee.vtyp
                                    ; ppos = pos}
                                , default_rowis ))
                        |> Stream.map clause
                        |> Stream.into (Vector.sink ()) in
                    let var = E.fresh_var typ in
                    let node : State.node = Test {matchee; clauses} in
                    Automaton.add states var.name {State.var; refcount = 1; frees = Some matchees; node};
                    var

                | Tuple typs ->
                    let width = Vector.length typs in
                    let pats = split_tuple pats coli width in
                    let matchee = Vector.get matchees coli in
                    let matchees'' = Vector.init width (fun i -> E.fresh_var (Vector.get typs i)) in
                    let matchees' = Vector.concat [Vector.sub matchees 0 coli; matchees''
                        ; Vector.sub matchees (coli + 1) (Vector.length matchees - (coli + 1))] in
                    let defs = Stream.from (Source.zip_with (fun (matchee' : var) index ->
                                let focusee = E.at pos matchee.vtyp (E.use matchee) in
                                S.Def ( pos, matchee'
                                    , E.at pos matchee'.vtyp (E.focus focusee index )))
                            (Vector.to_source matchees'')
                            (Source.count 0))
                        |> Stream.into (Vector.sink ()) in
                    let body = matcher' matchees' pats acceptors in
                    let var = E.fresh_var typ in
                    let node : State.node = Destructure {defs; body} in
                    Automaton.add states var.name {var; refcount = 1; frees = Some matchees; node};
                    var

                | Fn _ | Prim (Cell | SingleRep | Boxed | TypeIn | RowOf)
                | EmptyRow | PromotedTuple _ | PromotedArray _ -> failwith "unreachable"

                | _ -> failwith "TODO: pattern expansion")
            else begin
                let tmp_vars = Stream.from (Source.zip (Vector.to_source matchees) row)
                    |> Stream.filter (fun (_, pat) -> is_named pat)
                    |> Stream.map (function
                        | (tmp_var, {E.pterm = VarP src_var; _}) -> {tmp_var; src_var}
                        | _ -> failwith "unreachable")
                    |> Stream.into Sink.array in
                Array.sort (fun {src_var; _} {src_var = src_var'; _} ->
                    E.Var.compare src_var src_var'
                ) tmp_vars;
                let tmp_vars = Vector.of_array_unsafe tmp_vars in
                match Vector.get acceptors 0 with
                | {State.node = Final node; _} as acceptor ->
                    acceptor.refcount <- acceptor.refcount + 1;
                    acceptor.frees <- Some matchees;
                    node.tmp_vars <- Some tmp_vars;
                    acceptor.var
                | _ -> failwith "compiler bug: non-Final node as acceptor"
            end

        | None -> failwith "nonexhaustive matching" in

    let matchees = Vector.singleton matchee in
    let pats = Matrix.of_col (Vector.map (fun {pat; emit = _} -> pat) clauses) in
    let acceptors = Vector.map (fun {pat = _; emit} ->
        let var = E.fresh_var typ in
        let node : State.node = Final {tmp_vars = None; emit} in
        let state = {State.var; refcount = 0; frees = None; node} in
        Automaton.add states var.name state;
        state
    ) clauses in
    (states, matcher' matchees pats acceptors)

let emit pos codomain states start =
    let shareds = Name.Hashtbl.create 0 in

    let rec emit' state_name =
        let state : State.t = Automaton.find states state_name in

        let emit_shared ({var; frees = _; refcount = _; node} : State.t) = (* TODO: use `frees`? *)
            match node with
            | Final {tmp_vars; emit} -> emit (Shared var) (Option.get tmp_vars)
            | _ -> failwith "TODO: shared intermediate pattern matching state 1st encounter" in

        let emit_redirect ({var; refcount = _; frees = _; node} : State.t) =
            match node with
            | Final {tmp_vars; emit} -> emit (Redirect var) (Option.get tmp_vars)
            | _ -> failwith "TODO: emit_redirect to non-final state" in

        let emit_inline ({node; _} : State.t) = match node with
            | Test {matchee; clauses} ->
                E.at pos codomain
                    (E.match' (E.at pos matchee.vtyp (E.use matchee))
                        (clauses |> Vector.map (fun (pat, (target : var)) ->
                            {E.pat; body = emit' target.name})))
            | Destructure {defs; body} ->
                let expr = emit' body.name in
                {expr with term = E.let' (Vector.to_array defs) expr}
            | Final {tmp_vars; emit} -> emit Inline (Option.get tmp_vars) in

        if state.refcount > 1 && not (Name.Hashtbl.mem shareds state_name)
        then begin
            let f = emit_shared state in
            Name.Hashtbl.add shareds state_name (pos, state.var, f)
        end;

        if Name.Hashtbl.mem shareds state_name
        then emit_redirect state
        else emit_inline state in

    let body = emit' start in
    (* TODO: Warnings for redundant states (refcount = 0) *)
    {body with term = E.let' (Stream.from (Source.seq (Name.Hashtbl.to_seq_values shareds))
        |> Stream.map (fun def -> S.Def def)
        |> Stream.into Sink.array) body}

let expand_clauses : Util.span -> T.t -> expr -> clause' Vector.t -> expr
= fun pos codomain matchee clauses ->
    let var = E.fresh_var matchee.typ in
    let (states, start) = matcher pos codomain var clauses in
    let body = emit pos codomain states start.name in
    E.at pos codomain (E.let' [|Def (pos, var, matchee)|] body)

