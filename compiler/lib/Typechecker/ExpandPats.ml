open Streaming

module T = Fc.Type
module E = Fc.Term.Expr
type var = E.var
type expr = E.t
type pat = E.pat
type clause = E.clause
type def = Fc.Term.Stmt.def

(* TODO: Roll back eager `let` generation,
    `|Foo, 'Foo x|->` can be handled by substituting temp instead, i.e. `'Foo#0 x#1` *)
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
        | Destructure of var
        | Final of {index : int; body : expr}

    type t =
        { var : var
        ; mutable refcount : int
        ; mutable frees : var Vector.t option
        ; defs : def Array.t
        ; node : node }
end

module Automaton = struct
    include Name.Hashtbl
    type table = State.t t
    type t = table
end

module IntMap = Map.Make(Int)

let split_int : pat Matrix.t -> int -> IntSet.t IntMap.t * IntSet.t
= fun pats col ->
    let add_single singles n i = singles |> IntMap.update n (function
        | Some branch -> Some (IntSet.add i branch)
        | None -> Some (IntSet.singleton i)) in
    let step (singles, defaults) (i, (pat : pat)) = match pat.pterm with
        | ConstP (Int n) -> (add_single singles n i, defaults)
        | VarP _ | WildP -> (singles, IntSet.add i defaults)
        | ValuesP _ | ProxyP _ -> failwith "unreachable" in
    let (singles, defaults) =
        Stream.from (Source.zip (Source.count 0) (Option.get (Matrix.col col pats)))
        |> Stream.into (Sink.fold step (IntMap.empty, IntSet.empty)) in
    (IntMap.map (IntSet.union defaults) singles, defaults)

let split_tuple pats coli width =
    let subpats (pat : pat) = match pat.pterm with
        | ValuesP pats -> pats
        | VarP _ | WildP -> Vector.init width (fun _ -> {pat with pterm = E.WildP})
        | ProxyP _ | ConstP _ -> failwith "unreachable" in
    let cols' = Stream.from (Option.get (Matrix.col coli pats))
        |> Stream.map subpats
        |> Matrix.of_rows in
    Matrix.hcat [Matrix.sub_cols 0 (Some coli) pats; cols'; Matrix.sub_cols (coli + 1) None pats]

let is_trivial : pat -> bool = fun pat -> match pat.pterm with
    | VarP _ | WildP | ProxyP _ -> true
    | ValuesP _ | ConstP _ -> false

let is_named (pat : pat) = match pat.pterm with
    | VarP _ -> true
    | _ -> false

let rec matcher' : Util.span -> T.t -> Automaton.t -> var Vector.t -> pat Matrix.t -> State.t Vector.t -> var
= fun pos typ states matchees pats acceptors ->
    match Matrix.row 0 pats with
    | Some row ->
        let (coli, defs) = Stream.from (Source.zip row (Vector.to_source matchees))
            |> Stream.take_while (fun (pat, _) -> is_trivial pat)
            |> Stream.into (Sink.zip Sink.len
                (Sink.array
                |> Sink.premap (fun ((pat : pat), (matchee : var)) -> match pat.pterm with
                    | VarP var ->
                        let use = E.at pat.ppos matchee.vtyp (E.use matchee) in
                        (pat.ppos, var, use)
                    | _ -> failwith "unreachable")
                |> Sink.prefilter (fun (pat, _) -> is_named pat))) in
        if coli < Vector.length matchees then begin
            let row = Stream.concat
                (Stream.generate ~len: coli (fun i ->
                    let (ppos, _, {E.typ = ptyp; _}) = Array.get defs i in
                    {E.pterm = E.WildP; ptyp; ppos}))
                (Stream.drop coli (Stream.from row)) in
            let pats = Matrix.set_row 0 row pats in
            match (Vector.get matchees coli).vtyp with (* TODO: eval typ *)
            | Prim Int ->
                let (rows, default_rowis) = split_int pats coli in
                let matchee = Vector.get matchees coli in
                let matchees' = Vector.remove matchees coli in
                let pats = Matrix.remove_col coli pats in
                let clause (pat, rowis) =
                    let pats = Matrix.select_rows rowis pats in
                    let acceptors = Vector.select acceptors rowis in
                    (pat, matcher' pos typ states matchees' pats acceptors) in
                let clauses = Stream.concat
                        (Stream.from (Source.seq (IntMap.to_seq rows))
                            |> Stream.map (fun (n, rowis) ->
                                ( {E.pterm = E.ConstP (Int n); ptyp = matchee.vtyp; ppos = pos}
                                , rowis )))
                        (Stream.single ( {E.pterm = E.WildP; ptyp = matchee.vtyp; ppos = pos}
                                       , default_rowis ))
                    |> Stream.map clause
                    |> Stream.into (Vector.sink ()) in
                let var = E.fresh_var typ None in
                let node : State.node = Test {matchee; clauses} in
                Automaton.add states var.name {var; refcount = 1; frees = Some matchees; defs; node};
                var

            | Values typs ->
                let width = Vector.length typs in
                let pats = split_tuple pats coli width in
                let matchee = Vector.get matchees coli in
                let matchees'' = Vector.init width (fun i -> E.fresh_var (Vector.get typs i) None) in
                let matchees' = Vector.concat [Vector.sub matchees 0 coli; matchees''
                    ; Vector.sub matchees (coli + 1) (Vector.length matchees - (coli + 1))] in
                let defs = Stream.concat
                        (Stream.from (Source.array defs))
                        (Stream.from (Source.zip_with (fun (matchee' : var) index ->
                                let focusee = E.at pos matchee.vtyp (E.use matchee) in
                                ( pos, matchee'
                                , E.at pos matchee'.vtyp (E.focus focusee index )))
                            (Vector.to_source matchees'')
                            (Source.count 0)))
                    |> Stream.into Sink.array in
                let body = matcher' pos typ states matchees' pats acceptors in
                let var = E.fresh_var typ None in
                let node : State.node = Destructure body in
                Automaton.add states var.name {var; refcount = 1; frees = Some matchees; defs; node};
                var

            | Fn _ | Prim (Cell | SingleRep | Boxed | TypeIn | RowOf)
            | EmptyRow | PromotedValues _ | PromotedArray _ -> failwith "unreachable"

            | _ -> failwith "TODO: pattern expansion"

        end else begin
            let acceptor = Vector.get acceptors 0 in
            acceptor.refcount <- acceptor.refcount + 1;
            acceptor.frees <- Some matchees;
            Automaton.add states acceptor.var.name {acceptor with defs};
            acceptor.var
        end

    | None -> failwith "nonexhaustive matching"

let matcher : Util.span -> T.t -> var -> clause Vector.t -> Automaton.t * var
= fun pos typ matchee clauses ->
    let states = Automaton.create (Vector.length clauses) in
    let matchees = Vector.singleton matchee in
    let pats = Matrix.of_col (Vector.map (fun {E.pat; body = _} -> pat) clauses) in
    let acceptors = Vector.mapi (fun index {E.pat = _; body} ->
        let var = E.fresh_var body.typ (Some body) in
        let node : State.node = Final {index; body} in
        let defs = Array.init 0 (fun _ -> failwith "unreachable") in
        let state = {State.var; refcount = 0; frees = None; defs; node} in
        Automaton.add states var.name state;
        state
    ) clauses in
    (states, matcher' pos typ states matchees pats acceptors)

let rec emit' : Util.span -> T.t -> Automaton.t -> E.def Name.Hashtbl.t -> Name.t -> expr
= fun pos codomain states shareds state_name ->
    let {State.var; refcount; frees; defs; node} = Automaton.find states state_name in
    if Name.Hashtbl.mem shareds state_name then begin (* TODO: DRY: *)
        let frees = Option.get frees in
        let domain : T.t = Values (Vector.map (fun (fv : var) -> fv.vtyp) frees) in
        let ftyp = T.Pi { universals = Vector.empty
            ; domain = Ior.Right { edomain = domain 
                ; eff = EmptyRow } (* NOTE: effect does not matter any more... *)
            ; codomain } in
        let args = Stream.from (Vector.to_source frees)
            |> Stream.map (fun (var : var) -> E.at pos var.vtyp (E.use var))
            |> Stream.into (Sink.buffer (Vector.length frees)) in
        E.at pos codomain (E.app (E.at pos ftyp (E.use var)) Vector.empty
            (E.at pos domain (E.values args)))
    end else begin
        let body : expr = match node with
            | Test {matchee; clauses} ->
                E.at pos codomain
                    (E.match' (E.at pos matchee.vtyp (E.use matchee))
                        (clauses |> Vector.map (fun (pat, (target : var)) ->
                            {E.pat; body = emit' pos codomain states shareds target.name})))
            | Destructure body -> emit' pos codomain states shareds body.name
            | Final {index = _; body} -> body in
        (* FIXME: use `let'` but that breaks FwdRefs ATM.
         * Prerequisite: fix ExpandPats' emitting multiple defs of same `var` due to 'eager letrec generation'. *)
        let body = {body with term = E.letrec defs body} in
        if refcount = 1
        then body
        else begin
            let pos = body.pos in
            let frees = Option.get frees in
            let domain : T.t = Values (Vector.map (fun (fv : var) -> fv.vtyp) frees) in
            let ftyp = T.Pi { universals = Vector.empty
                ; domain = Ior.Right { edomain = domain 
                    ; eff = EmptyRow } (* NOTE: effect does not matter any more... *)
                ; codomain } in
            let param = E.fresh_var domain None in
            let f : expr = E.at pos ftyp (E.fn Vector.empty param body) in
            Name.Hashtbl.add shareds state_name (body.pos, var, f);
            let args = Stream.from (Vector.to_source frees)
                |> Stream.map (fun (var : var) -> E.at pos var.vtyp (E.use var))
                |> Stream.into (Sink.buffer (Vector.length frees)) in
            E.at pos codomain (E.app (E.at pos ftyp (E.use var)) Vector.empty
                (E.at pos domain (E.values args)))
        end
    end

let emit : Util.span -> T.t -> Automaton.t -> Name.t -> expr
= fun pos codomain states start ->
    let shareds = Name.Hashtbl.create 0 in
    let body = emit' pos codomain states shareds start in
    (* TODO: Warnings for redundant states (refcount = 0) *)
    {body with term = E.letrec (Stream.from (Source.seq (Name.Hashtbl.to_seq_values shareds))
        |> Stream.into Sink.array) body}

let expand_clauses : Util.span -> T.t -> expr -> clause Vector.t -> expr
= fun pos codomain matchee clauses ->
    let var = E.fresh_var matchee.typ (Some matchee) in
    let (states, start) = matcher pos codomain var clauses in
    let body = emit pos codomain states start.name in
    E.at pos codomain (E.let' [|Def (pos, var, matchee)|] body)

