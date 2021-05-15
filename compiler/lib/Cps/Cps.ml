open Streaming

open Asserts

module S = CpsSigs

type span = Util.span

module ContId = struct
    include Id.Make ()

    let to_doc id = PPrint.(percent ^^ to_doc id)
end

module Type = struct
    type expr_id = Name.t
    type cont_id = ContId.t

    type kind = Fc.Type.kind
    type param = Fc.Type.def

    type t =
        | Exists of kind Vector1.t * t
        | Pair of {fst : t; snd : t}
        | Pi of {universals : kind Vector.t; domain : t Vector.t}
        | Record of t
        | Variant of t
        | With of {base : t; label : Name.t; field : t}
        | EmptyRow
        | Proxy of t
        | Prim of Prim.t
        | Fn of kind * t
        | App of t * t
        | Bv of Fc.Type.bv
        | TParam of {label : cont_id; index : int}
        | Abstract of kind
        | Existing of {value : expr_id; index : int}

    let kind_to_doc = Fc.Type.kind_to_doc
    let param_to_doc = Fc.Type.def_to_doc

    let rec to_doc typ =
        let open PPrint in
        match typ with
        | Exists (existentials, body) ->
            prefix 4 1
                (string "exists" ^^ blank 1
                ^^ surround_separate_map 4 0 empty
                        langle (comma ^^ break 1) (rangle ^^ break 1)
                        kind_to_doc (Vector1.to_list existentials))
                (to_doc body)

        | Pair {fst; snd} ->
            surround_separate_map 4 0 (parens colon)
                (lparen ^^ colon) (comma ^^ break 1) rparen
                to_doc [fst; snd]

        | Pi {universals; domain} ->
            prefix 4 1 (string "pi")
                (surround_separate_map 4 0 empty
                    langle (comma ^^ break 1) (rangle ^^ break 1)
                    kind_to_doc (Vector.to_list universals)
                ^^ surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ break 1) rparen
                    to_doc (Vector.to_list domain))

        | Record row -> braces (to_doc row)

        | Variant row -> parens (prefix 4 1 sharp (to_doc row))

        | With {base; label; field} ->
            infix 4 1 (string "with") (to_doc base)
                (infix 4 1 equals (Name.to_doc label) (to_doc field))

        | EmptyRow -> parens bar

        | Proxy carrie -> brackets (prefix 4 1 equals (to_doc carrie))

        | Prim p -> string "__" ^^ Prim.to_doc p

        | Fn (param, body) ->
            infix 4 1 dot (string "fn" ^^ blank 1 ^^ kind_to_doc param) (to_doc body)

        | App (callee, arg) -> parens (to_doc callee) ^^ blank 1 ^^ parens (to_doc arg)

        | Bv _ -> todo None (*Fc.Type.bv_to_doc bv*)

        | TParam {label; index} -> 
            infix 4 1 (string "param") (ContId.to_doc label) (string (Int.to_string index))
            |> parens

        | Abstract kind -> string "abstract" ^/^ kind_to_doc kind

        | Existing {value; index} ->
            infix 4 1 (string "existing") (Name.to_doc value) (string (Int.to_string index))
            |> parens

    let coercion_to_doc = Fc.Type.coercion_to_doc' to_doc
end

module Expr = struct
    type cont_id = ContId.t
    module Type = Type

    module Id = Name

    type t' =
        | PrimApp of {op : Primop.t; universals : Type.t Vector.t; args : Id.t Vector.t}
        | Record of (Name.t * Id.t) Vector.t
        | With of {base : Id.t; label: Name.t; field : Id.t}
        | Where of {base : Id.t; fields : (Name.t * Id.t) Vector.t}
        | Select of {selectee : Id.t; field : Name.t}
        | Proxy of Type.t
        | Label of cont_id
        | Param of {label : cont_id; index : int}
        | Cast of {castee : Id.t; coercion : Type.t Fc.Type.coercion}
        | Pack of {existentials : Type.t Vector1.t; impl : Id.t}
        | Unpack of Id.t
        | Const of Const.t

    type t =
        { pos : span
        ; cont : cont_id option
        ; typ : Type.t
        ; term : t' }

    let field_to_doc (label, field) =
        PPrint.(infix 4 1 equals (Name.to_doc label) (Id.to_doc field))

    let term_to_doc term =
        let open PPrint in
        match term with
        | PrimApp {op; universals; args} ->
            prefix 4 1 (string "__" ^^ Primop.to_doc op)
                (surround_separate_map 4 0 empty
                    langle (comma ^^ break 1) (rangle ^^ blank 1)
                    Type.to_doc (Vector.to_list universals)
                ^^ surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ break 1) rparen
                    Id.to_doc (Vector.to_list args))

        | Record fields ->
            surround_separate_map 4 0 (braces empty)
                lbrace (comma ^^ break 1) rbrace
                field_to_doc (Vector.to_list fields)

        | With {base; label; field} ->
            infix 4 1 (string "with") (Id.to_doc base)
                (infix 4 1 equals (Name.to_doc label) (Id.to_doc field))

        | Where {base; fields} ->
            infix 4 1 (string "where") (Id.to_doc base)
                (surround_separate_map 4 0 (braces empty)
                    lbrace (comma ^^ break 1) rbrace
                    field_to_doc (Vector.to_list fields))

        | Select {selectee; field} -> 
            infix 4 1 dot (Id.to_doc selectee) (Name.to_doc field)
        | Proxy typ -> brackets (equals ^^ blank 1 ^^ Type.to_doc typ)
        | Label label -> string "fn" ^^ blank 1 ^^ ContId.to_doc label
        | Param {label; index} ->
            infix 4 1 (string "param") (ContId.to_doc label) (string (Int.to_string index))

        | Cast {castee; coercion} -> 
            infix 4 1 (string "|>") (Id.to_doc castee) (Type.coercion_to_doc coercion)

        | Pack {existentials; impl} ->
            prefix 4 1
                (string "pack" ^/^ surround_separate_map 4 0 empty
                    langle (comma ^^ break 1) (rangle ^^ blank 1)
                    Type.to_doc (Vector1.to_list existentials))
                (Id.to_doc impl)
        | Unpack packed -> string "unpack" ^/^ Id.to_doc packed

        | Const c -> Const.to_doc c

    let to_doc expr = term_to_doc expr.term

    let def_to_doc id expr =
        let open PPrint in
        infix 4 1 equals (infix 4 1 colon (Id.to_doc id) (Type.to_doc expr.typ))
            (to_doc expr)

    let iter_labels' f = function
        | Label label | Param {label; index = _} -> f label
        | PrimApp _ | Record _ | With _ | Where _ | Select _ | Proxy _
        | Cast _ | Pack _ | Unpack _ | Const _ -> ()

    let iter_labels f expr = iter_labels' f expr.term

    let iter_uses' f = function
        | PrimApp {universals = _; op = _; args} -> Vector.iter f args
        | Record fields -> Vector.iter (fun (_, use) -> f use) fields
        | Where {base; fields} -> f base; Vector.iter (fun (_, use) -> f use) fields
        | With {base; label = _; field} -> f base; f field
        | Select {selectee = use; field = _} -> f use
        | Cast {castee; coercion = _} -> f castee
        | Pack {existentials = _; impl} -> f impl
        | Unpack packed -> f packed
        | Proxy _ | Label _ | Param _ | Const _ -> ()

    let iter_uses f expr = iter_uses' f expr.term

    let map_uses' f term = match term with
        | PrimApp {universals; op; args} ->
            let (noop, args) = Stream.from (Vector.to_source args)
                |> Stream.map (fun arg -> let arg' = f arg in (arg' == arg, arg'))
                |> Stream.into (Sink.unzip (Sink.fold (&&) true) (Vector.sink ())) in
            if noop then term else PrimApp {universals; op; args}

        | Record fields ->
            let (noop, fields) = Stream.from (Vector.to_source fields)
                |> Stream.map (fun (k, v) -> let v' = f v in (v' == v, (k, v')))
                |> Stream.into (Sink.unzip (Sink.fold (&&) true) (Vector.sink ())) in
            if noop then term else Record fields

        | Where {base; fields} ->
            let base' = f base in
            let (noop, fields) = Stream.from (Vector.to_source fields)
                |> Stream.map (fun (k, v) -> let v' = f v in (v' == v, (k, v')))
                |> Stream.into (Sink.unzip (Sink.fold (&&) true) (Vector.sink ())) in
            if base' == base && noop then term else Where {base = base'; fields}

        | With {base; label; field} ->
            let base' = f base in
            let field' = f field in
            if base' == base && field' == field
            then term
            else With {base = base'; label; field = field'}

        | Select {selectee; field} ->
            let selectee' = f selectee in
            if selectee' == selectee then term else Select {selectee = selectee'; field}

        | Cast {castee; coercion} ->
            let castee' = f castee in
            if castee' == castee then term else Cast {castee = castee'; coercion}

        | Pack {existentials; impl} ->
            let impl' = f impl in
            if impl' == impl then term else Pack {existentials; impl = impl'}

        | Unpack packed ->
            let packed' = f packed in
            if packed' == packed then term else Unpack packed'

        | Proxy _ | Label _ | Param _ | Const _ -> term

    let map_uses f expr = {expr with term = map_uses' f expr.term}
end

module Pattern = struct
    type t =
        | Const of Const.t
        | Wild

    let to_doc = function
        | Const c -> Const.to_doc c
        | Wild -> PPrint.underscore
end

module Transfer = struct
    module Type = Type
    module Pattern = Pattern
    type expr_id = Expr.Id.t
    type cont_id = ContId.t

    type clause = {pat : Pattern.t; dest : cont_id}

    type t' =
        | Goto of {callee : cont_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Jump of {callee : expr_id; universals : Type.t Vector.t; args : expr_id Vector.t}
        | Match of {matchee : expr_id; state : expr_id; clauses : clause Vector.t}
        | PrimApp of {op : Branchop.t; universals : Type.t Vector.t
            ; state : expr_id; args : expr_id Vector.t; clauses : clause Vector.t}
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

    let clause_to_doc {pat; dest} =
        PPrint.(prefix 4 1 bar
            (infix 4 1 (string "=>") (Pattern.to_doc pat) (ContId.to_doc dest)))

    let to_doc (transfer : t) =
        let open PPrint in
        match transfer.term with
        | Goto {universals; callee; args} ->
            prefix 4 1 (string "goto" ^^ blank 1 ^^ ContId.to_doc callee)
                (args_to_doc universals args)

        | Jump {universals; callee; args} ->
            prefix 4 1 (string "jump" ^^ blank 1 ^^ Expr.Id.to_doc callee)
                (args_to_doc universals args)

        | Match {matchee; state; clauses} ->
            string "match" ^^ blank 1 ^^
            parens (Expr.Id.to_doc state ^^ comma ^^ blank 1
                ^^ Expr.Id.to_doc matchee) ^^ blank 1
            ^^ surround_separate_map 4 0 (braces empty)
                lbrace hardline rbrace clause_to_doc (Vector.to_list clauses)

        | PrimApp {op; universals; state; args; clauses} ->
            prefix 4 1 (string "__" ^^ Branchop.to_doc op)
                (surround_separate_map 4 0 empty
                    langle (comma ^^ break 1) (rangle ^^ blank 1)
                    Type.to_doc (Vector.to_list universals)
                ^^ Expr.Id.to_doc state ^^ blank 1
                ^^ surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ break 1) rparen
                    Expr.Id.to_doc (Vector.to_list args)) ^^ blank 1
            ^^ surround_separate_map 4 0 (braces empty)
                lbrace hardline rbrace clause_to_doc (Vector.to_list clauses)

        | Return (universals, args) ->
            prefix 4 1 (string "return") (args_to_doc universals args)

    let iter_labels f (transfer : t) = match transfer.term with
        | Goto {universals = _; callee; args = _} -> f callee
        | Match {matchee = _; state = _; clauses}
        | PrimApp {op = _; universals = _; state = _; args = _; clauses} ->
            Vector.iter (fun {pat = _; dest} -> f dest) clauses
        | Jump _ | Return _ -> ()

    let iter_uses f (transfer : t) = match transfer.term with
        | Goto {universals = _; callee = _; args} -> Vector.iter f args
        | Jump {universals = _; callee; args} -> f callee; Vector.iter f args
        | Match {matchee; state; clauses = _} -> f matchee; f state
        | PrimApp {op = _; universals = _; state; args; clauses = _} ->
            f state; Vector.iter f args
        | Return (_, args) -> Vector.iter f args

    let map_uses f (transfer : t) =
        let term = match transfer.term with
            | Goto {universals; callee; args} ->
                Goto {universals; callee; args = Vector.map f args}
            | Jump {universals; callee; args} ->
                Jump {universals; callee = f callee; args = Vector.map f args}
            | Match {matchee; state; clauses} ->
                Match {matchee = f matchee; state = f state; clauses}
            | PrimApp {op; universals; args; state; clauses} ->
                PrimApp {op; universals; args = Vector.map f args
                    ; state = f state; clauses}
            | Return (universals, args) -> Return (universals, Vector.map f args) in
        {transfer with term}
end

module Cont = struct
    module Type = Type
    module Transfer = Transfer

    module Id = ContId

    type t =
        { pos : span
        ; name : Name.t option
        ; universals : Type.param Vector.t
        ; params : Type.t Vector.t
        ; body : Transfer.t }

    let to_doc {pos = _; name; universals; params; body} ~exprs_doc =
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
        ^^ blank 1 ^^ surround 4 1
            lbrace (exprs_doc ^^ Transfer.to_doc body) rbrace

    let def_to_doc id cont ~exprs_doc =
        PPrint.(Id.to_doc id ^^ blank 1 ^^ equals ^^ blank 1 ^^ to_doc cont ~exprs_doc)
end

module Program = struct
    module Type = Type
    module Expr = Expr
    module Cont = Cont

    module Exprs = Expr.Id.HashMap
    module Conts = Cont.Id.HashMap

    type t =
        { type_fns : Type.param Vector.t
        ; exprs : Expr.t Exprs.t
        ; conts : Cont.t Conts.t
        ; main : Cont.Id.t }

    type builder =
        { type_fns : Type.param Vector.t
        ; mutable exprs : Expr.t Exprs.t
        ; mutable conts : Cont.t Conts.t
        ; transient : CCHashTrie.Transient.t }

    let to_doc {type_fns; exprs; conts; main} =
        let open PPrint in
        let cont_exprs = Cont.Id.Hashtbl.create (Conts.cardinal conts) in
        Exprs.iter ~f: (fun id (expr : Expr.t) -> match expr.cont with
            | Some cont_id ->
                Cont.Id.Hashtbl.replace cont_exprs cont_id 
                    (Cont.Id.Hashtbl.find_opt cont_exprs cont_id
                    |> Option.value ~default: []
                    |> (fun kvs -> (id, expr) :: kvs))
            | None -> ()
        ) exprs;
        let cont_exprs_doc id =
            concat_map (fun (id, expr) -> Expr.def_to_doc id expr ^^ semi ^^ hardline)
                (Cont.Id.Hashtbl.find_opt cont_exprs id |> Option.value ~default: []) in

        separate_map (twice hardline) (fun typedef ->
            string "type" ^^ blank 1 ^^ Type.param_to_doc typedef ^^ semi
        ) (Vector.to_list type_fns) ^^ twice (twice hardline)
        ^^ separate_map (twice hardline) (fun (id, expr) ->
            Expr.def_to_doc id expr ^^ semi
        ) (Exprs.to_list exprs (* orphan defs *)
            |> List.filter (fun (_, (expr : Expr.t)) -> Option.is_none expr.cont))
        ^^ twice (twice hardline)
        ^^ separate_map (twice hardline) (fun (id, cont) ->
            Cont.def_to_doc id cont ~exprs_doc: (cont_exprs_doc id)
        ) (Conts.to_list conts (* non-main conts *)
            |> List.filter (fun (id, _) -> not (Cont.Id.equal id main)))
        ^^ twice hardline ^^ Cont.def_to_doc main (Conts.get_exn main conts)
            ~exprs_doc: (cont_exprs_doc main)

    let type_fns (program : t) = program.type_fns

    let main program = program.main

    let exports {type_fns = _; exprs = _; conts = _; main} = Source.single main

    let cont (program : t) label = Conts.get_exn label program.conts

    let conts (program : t) =
        let gen = Conts.to_gen program.conts in
        Stream.unfold () (fun () -> gen () |> Option.map (fun kv -> (kv, ())))

    let expr (program : t) id = Exprs.get_exn id program.exprs

    let exprs (program : t) =
        let gen = Exprs.to_gen program.exprs in
        Stream.unfold () (fun () -> gen () |> Option.map (fun kv -> (kv, ())))

    let usecounts ({type_fns = _; exprs = _; conts = _; main} as program) =
        let transient = CCHashTrie.Transient.create () in
        let visited = Cont.Id.HashSet.create 0 in

        let rec visit_use counts id =
            let visit_expr counts id =
                if Exprs.mem id counts
                then counts
                else begin
                    let {Expr.pos = _; typ = _; cont = _; term} = expr program id in
                    match term with
                    | PrimApp {op = _; universals = _; args = children} ->
                        Vector.fold visit_use counts children
                    | Select {selectee = child; field = _}
                    | Cast {castee = child; coercion = _}
                    | Pack {existentials = _; impl = child}
                    | Unpack child -> visit_use counts child
                    | Record fields -> Vector.fold (fun counts (_, child) ->
                            visit_use counts child
                        ) counts fields
                    | Where {base; fields} -> Vector.fold (fun counts (_, child) ->
                            visit_use counts child
                        ) (visit_use counts base) fields
                    | With {base; label = _; field} -> visit_use (visit_use counts base) field
                    | Label label
                    | Param {label; index = _} -> visit_cont counts label
                    | Proxy _ | Const _ -> counts
                end in

            let counts = visit_expr counts id in
            Exprs.update_mut ~id: transient id counts ~f: (function
                | Some n -> Some (n + 1)
                | None -> Some 1)

        and visit_clause counts {Transfer.pat = _; dest} = visit_cont counts dest

        and visit_transfer counts {Transfer.pos = _; term} = match term with
            | Goto {universals = _; callee = _; args}
            | Return (_, args) -> Vector.fold visit_use counts args
            | Jump {universals = _; callee; args} ->
                Vector.fold visit_use (visit_use counts callee) args
            | Match {matchee; state; clauses} ->
                let counts = visit_use (visit_use counts matchee) state in
                Vector.fold visit_clause counts clauses
            | PrimApp {op = _; universals = _; state; args; clauses} ->
                let counts = Vector.fold visit_use (visit_use counts state) args in
                Vector.fold visit_clause counts clauses

        and visit_cont counts label =
            if Cont.Id.HashSet.mem visited label
            then counts
            else begin
                Cont.Id.HashSet.insert visited label;
                let {Cont.pos = _; name = _; universals = _; params = _; body} =
                    cont program label in
                visit_transfer counts body
            end in

        visit_cont Exprs.empty main

    type transient =
        { type_fns : Type.param Vector.t
        ; mutable exprs : Expr.t Exprs.t
        ; mutable conts : Cont.t Conts.t
        ; main : Cont.Id.t
        ; transient : CCHashTrie.Transient.t }

    module Transient = struct
        let from ({type_fns; exprs; conts; main} : t) =
            { type_fns; exprs; conts; main
            ; transient = CCHashTrie.Transient.create () }

        let persist {type_fns; exprs; conts; main; transient} =
            CCHashTrie.Transient.freeze transient;
            {type_fns; exprs; conts; main}

        let exprs (program : transient) =
            let gen = Exprs.to_gen program.exprs in
            Stream.unfold () (fun () -> gen () |> Option.map (fun kv -> (kv, ())))

        let add_expr program id expr =
            program.exprs <-
                Exprs.add_mut ~id: program.transient id expr program.exprs

        let add_cont program label cont =
            program.conts <-
                Conts.add_mut ~id: program.transient label cont program.conts

        type t = transient
    end

    module Builder = struct
        let create type_fns =
            { type_fns
            ; exprs = Exprs.empty
            ; conts = Conts.empty
            ; transient = CCHashTrie.Transient.create () }

        let expr (builder : builder) id = Exprs.get_exn id builder.exprs

        let express_as (builder : builder) id expr =
            builder.exprs <- Exprs.add_mut ~id: builder.transient id expr builder.exprs

        let express builder (e : Expr.t) =
            (* TODO: More 'peephole' optimization (constant folding, GVN etc.): *)
            let folded = match e.term with
                | PrimApp {op = Fst; universals = _; args} ->
                    (match (expr builder (Vector.get args 0)).term with
                    | PrimApp {op = Pair; universals = _; args = fields} ->
                        Some (Vector.get fields 0)
                    | _ -> None)
                | PrimApp {op = Snd; universals = _; args} ->
                    (match (expr builder (Vector.get args 0)).term with
                    | PrimApp {op = Pair; universals = _; args = fields} ->
                        Some (Vector.get fields 1)
                    | _ -> None)

                | _ -> None in
            match folded with
            | Some id -> id
            | None ->
                let id = Expr.Id.fresh () in
                express_as builder id e;
                id

        let add_cont (builder : builder) id k =
            builder.conts <- Conts.add_mut ~id: builder.transient id k builder.conts

        let build ({type_fns; exprs; transient; conts} : builder) main =
            CCHashTrie.Transient.freeze transient;
            {type_fns; exprs; conts; main}

        type t = builder
    end
end

