open Streaming

type span = Util.span

module Type = Cps.Type

module Expr = struct
    type t = Cps.Expr.t'

    let to_doc = Cps.Expr.term_to_doc

    let is_pure : t -> bool = function
        | Values _ | Focus _ | Record _ | With _ | Where _ | Select _
        | Proxy _ | Label _ | Param _ | Const _ -> true

    let iter_uses = Cps.Expr.iter_uses'
    let iter_labels = Cps.Expr.iter_labels'

    module Id = Cps.Expr.Id
end

module Stmt = struct
    module Type = Type
    module Expr = Expr
    type var = Expr.Id.t

    type t' =
        | Def of var * Expr.t
        | Expr of Expr.t

    type t = {pos : span; typ : Type.t; term : t'}

    let to_doc {pos = _; typ; term} = match term with
        | Def (var, expr) ->
            PPrint.(infix 4 1 equals
                (infix 4 1 colon (Expr.Id.to_doc var) (Type.to_doc typ))
                (Expr.to_doc expr))
        | Expr expr -> Expr.to_doc expr

    let iter_uses f (stmt : t) = match stmt.term with
        | Def (_, expr) | Expr expr -> Expr.iter_uses f expr

    let iter_labels f (stmt : t) = match stmt.term with
        | Def (_, expr) | Expr expr -> Expr.iter_labels f expr
end

module Transfer = struct
    module Type = Type
    module Pattern = Cps.Pattern
    type expr_id = Expr.Id.t
    type cont_id = Cps.ContId.t

    type clause = Cps.Transfer.clause

    type t' =
        | Goto of {callee : cont_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Jump of {callee : expr_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Match of {matchee : expr_id; clauses : clause Vector.t}
        | PrimApp of {op : Primop.t; universals : Type.t Vector.t
            ; args : expr_id Vector.t; clauses : clause Vector.t}
        | Return of Type.t Vector.t * expr_id Vector.t

    type t = {pos : span; term : t'}

    let args_to_doc universals args =
        let open PPrint in
        surround_separate_map 4 0 empty
            langle (comma ^^ break 1) (rangle ^^ blank 1)
            Type.to_doc (Vector.to_list universals)
        ^^ surround_separate_map 4 0 (parens empty)
            lparen (comma ^^ break 1) rparen
            Expr.Id.to_doc (Vector.to_list args)

    let clause_to_doc ({pat; dest} : clause) =
        PPrint.(prefix 4 1 bar
            (infix 4 1 (string "=>") (Cps.Pattern.to_doc pat) (Cps.ContId.to_doc dest)))

    let to_doc (transfer : t) =
        let open PPrint in
        match transfer.term with
        | Goto {universals; callee; args} ->
            prefix 4 1 (string "goto" ^^ blank 1 ^^ Cps.ContId.to_doc callee)
                (args_to_doc universals args)

        | Jump {universals; callee; args} ->
            prefix 4 1 (string "jump" ^^ blank 1 ^^ Expr.Id.to_doc callee)
                (args_to_doc universals args)

        | Match {matchee; clauses} ->
            string "match" ^^ blank 1
            ^^ Expr.Id.to_doc matchee ^^ blank 1
            ^^ surround_separate_map 4 0 (braces empty)
                lbrace hardline rbrace clause_to_doc (Vector.to_list clauses)

        | PrimApp {op; universals; args; clauses} ->
            prefix 4 1 (string "__" ^^ Primop.to_doc op)
                (surround_separate_map 4 0 empty
                    langle (comma ^^ break 1) (rangle ^^ blank 1)
                    Type.to_doc (Vector.to_list universals)
                ^^ surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ break 1) (rparen ^^ blank 1)
                    Expr.Id.to_doc (Vector.to_list args)
                ^^ surround_separate_map 4 0 (braces empty)
                    lbrace hardline rbrace clause_to_doc (Vector.to_list clauses))

        | Return (universals, args) ->
            prefix 4 1 (string "return") (args_to_doc universals args)


    let iter_labels f (transfer : t) = match transfer.term with
        | Goto {universals = _; callee; args = _} -> f callee
        | Match {matchee = _; clauses}
        | PrimApp {op = _; universals = _; args = _; clauses} ->
            Vector.iter (fun {Cps.Transfer.pat = _; dest} -> f dest) clauses
        | Jump _ | Return _ -> ()

    let iter_uses f (transfer : t) = match transfer.term with
        | Goto {universals = _; callee = _; args} -> Vector.iter f args
        | Jump {universals = _; callee; args} -> f callee; Vector.iter f args
        | Match {matchee; clauses = _} -> f matchee
        | PrimApp {op = _; universals = _; args; clauses = _} -> Vector.iter f args
        | Return (_, args) -> Vector.iter f args
end


module Cont = struct
    module Type = Type
    module Stmt = Stmt
    module Transfer = Transfer

    type builder =
        { pos : span
        ; name : Name.t option
        ; universals : Type.param Vector.t
        ; params : Type.t Vector.t
        ; stmts : Stmt.t CCVector.vector
        ; mutable transfer : Transfer.t option }

    type t =
        { pos : span
        ; name : Name.t option
        ; universals : Type.param Vector.t
        ; params : Type.t Vector.t
        ; stmts : Stmt.t Vector.t
        ; transfer : Transfer.t }

    let to_doc {pos = _; name; universals; params; stmts; transfer} =
        let open PPrint in
        string "function" ^^ blank 1
        ^^ Option.fold ~some: (fun name -> Name.to_doc name ^^ blank 1)
            ~none: empty name
        ^^ surround_separate_map 4 0 empty
            langle (comma ^^ break 1) (rangle ^^ blank 1)
            Type.param_to_doc (Vector.to_list universals)
        ^^ surround_separate_map 4 0 (parens empty)
            lparen (comma ^^ break 1) rparen
            Type.to_doc (Vector.to_list params)
        ^^ blank 1 ^^ surround 4 1 lbrace
            (separate_map (semi ^^ hardline) Stmt.to_doc (Vector.to_list stmts)
            ^^ hardline ^^ Transfer.to_doc transfer)
            rbrace

    let def_to_doc id cont =
        PPrint.(Cps.Cont.Id.to_doc id ^^ blank 1 ^^ equals ^^ blank 1 ^^ to_doc cont)

    module Builder = struct
        let create ({pos; name; universals; params; body = _} : Cps.Cont.t) : builder =
            { pos; name; universals; params
            ; stmts = CCVector.create (); transfer = None }

        let define ({stmts; _} : builder) stmt = CCVector.push stmts stmt

        let set_transfer (builder : builder) transfer =
            builder.transfer <- Some transfer

        let build ({pos; name; universals; params; stmts; transfer} : builder) =
            { pos; name; universals; params; transfer = Option.get transfer
            ; stmts = stmts |> CCVector.to_array |> Vector.of_array_unsafe }

        type t = builder
    end

    module Id = Cps.Cont.Id
end

module Program = struct
    module Stmt = Stmt
    module Transfer = Transfer
    module Cont = Cont

    module Conts = Cont.Id.HashMap

    type t =
        { type_fns : Type.param Vector.t
        ; conts : Cont.t Conts.t
        ; main : Cont.Id.t }

    let to_doc {type_fns; conts; main} =
        let open PPrint in
        separate_map (twice hardline) (fun typedef ->
            string "type" ^^ blank 1 ^^ Type.param_to_doc typedef ^^ semi
        ) (Vector.to_list type_fns) ^^ twice (twice hardline)
        ^^ twice (twice hardline)
        ^^ separate_map (twice hardline) (fun (id, cont) ->
            Cont.def_to_doc id cont
        ) (Conts.to_list conts
            |> List.filter (fun (id, _) -> not (Cont.Id.equal id main)))
        ^^ twice hardline ^^ Cont.def_to_doc main (Conts.get_exn main conts)

    let exports program = Source.single program.main

    let cont program label = Conts.get_exn label program.conts

    type builder =
        { type_fns : Type.param Vector.t
        ; mutable conts : Cont.Builder.t Conts.t
        ; main : Cont.Id.t
        ; transient : CCHashTrie.Transient.t }

    module Builder = struct
        let create type_fns main =
            { type_fns
            ; conts = Conts.empty
            ; transient = CCHashTrie.Transient.create ()
            ; main }

        let add_cont ({transient; _} as builder) label cont =
            let cont_builder = Cont.Builder.create cont in
            builder.conts <- Conts.add_mut ~id: transient label cont_builder builder.conts

        let cont_mem {conts; _} label = Conts.mem label conts

        let define {conts; _} label stmt =
            Cont.Builder.define (Conts.get_exn label conts) stmt

        let set_transfer {conts; _} label transfer =
            Cont.Builder.set_transfer (Conts.get_exn label conts) transfer

        let build {type_fns; conts; main; transient} =
            let conts = Conts.fold ~f: (fun conts label builder ->
                Conts.add_mut ~id: transient label (Cont.Builder.build builder) conts
            ) ~x: Conts.empty conts in
            CCHashTrie.Transient.freeze transient;
            {type_fns; conts; main}
        
        type t = builder
    end
end

