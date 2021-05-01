open Streaming

module Tx = Transactional
module Type = FcType.Type

let ref = Tx.Ref.ref
let (!) = Tx.Ref.(!)

module rec Expr : sig
    include FcSigs.EXPR
        with type def = Stmt.def
        with type stmt = Stmt.t
        with type coercer = Coercer.t

    val def_to_doc : var -> PPrint.document
end = struct
    type def = Stmt.def
    type stmt = Stmt.t
    type coercer = Coercer.t

    type var = {plicity : Util.plicity; name : Name.t; vtyp : Type.t}

    type t =
        { term : t'
        ; mutable parent : t option
        ; typ : Type.t
        ; pos : Util.span }

    and t' =
        | Tuple of t array
        | Focus of {mutable focusee : t; index : int}

        | Fn of {universals : Type.def Vector.t; param : var; mutable body : t}
        | App of {mutable callee : t; universals : Type.t Vector.t; mutable arg : t}
        | PrimApp of {op : Primop.t; universals : Type.t Vector.t; mutable arg : t}
        | PrimBranch of {op : Branchop.t; universals : Type.t Vector.t; mutable arg : t
            ; clauses : prim_clause Vector.t}

        | Let of {defs : stmt Array1.t; mutable body : t}
        | Letrec of {defs : def Array1.t; mutable body : t}
        | LetType of {typedefs : Type.def Vector1.t; mutable body : t}
        | Match of {mutable matchee : t; clauses : clause Vector.t}

        | Axiom of { axioms : (Name.t * Type.kind Vector.t * Type.t * Type.t) Vector1.t
            ; mutable body : t }
        | Cast of {mutable castee : t; coercion : Type.t Type.coercion}

        | Pack of {existentials : Type.t Vector1.t; mutable impl : t}
        | Unpack of { existentials : Type.def Vector1.t; var : var; mutable value : t
            ; mutable body : t }

        | Record of (Name.t * t) array
        | Where of {mutable base : t; fields : (Name.t * t) Array1.t}
        | With of {mutable base : t; label : Name.t; mutable field : t}
        | Select of {mutable selectee : t; label : Name.t}

        | Proxy of Type.t
        | Const of Const.t

        | Use of var

        | Convert of coercer Tx.Ref.t * t

    and clause = {pat : pat; mutable body : t}
    and prim_clause = {res : var option; prim_body : t}

    and pat = {pterm: pat'; ptyp : Type.t; ppos : Util.span}
    and pat' =
        | TupleP of pat Vector.t
        | ProxyP of Type.t
        | ConstP of Const.t
        | VarP of var
        | WildP of Name.t

    let var_to_doc (var : var) = Name.to_doc var.name

    let def_to_doc (var : var) =
        PPrint.(infix 4 1 colon (var_to_doc var) (Type.to_doc var.vtyp))

    let w_prec = 3
    let cast_prec = 2
    let app_prec = 1
    let pack_prec = app_prec
    let dot_prec = 0

    let rec to_doc expr =
        let rec to_doc_prec prec expr = Util.with_prec to_docs prec expr

            and to_docs expr =
            let open PPrint in

            match expr.term with
            | With {base; label; field} ->
                let op = string "with" ^^ blank 1 ^^ Name.to_doc label ^^ blank 1 ^^ equals in
                InfixL {prec = w_prec; l = base; op; r = field}

            | Where {base; fields} ->
                let fields_doc = surround_separate_map 4 0 (braces empty)
                    lbrace (semi ^^ break 1) rbrace
                    (fun (label, field) ->
                        infix 4 1 equals (Name.to_doc label) (to_doc field))
                    (Array1.to_list fields) in
                Postfix {prec = w_prec; arg = base; op = string "where" ^^ blank 1 ^^ fields_doc}

            | Cast {castee; coercion} ->
                Postfix {prec = cast_prec; arg = castee
                    ; op = prefix 4 1 (string "|>") (Type.coercion_to_doc coercion)}

            | App {callee; universals; arg} ->
                if Vector.length universals = 0
                then Prefix {prec = app_prec; op = to_doc_prec app_prec callee; arg} (* HACK *)
                else begin
                    let op = surround_separate_map 4 0 empty
                        langle (comma ^^ break 1) rangle
                        Type.to_doc (Vector.to_list universals) in
                    InfixL {prec = app_prec; l = callee; op; r = arg}
                end

            | Convert (_, expr) -> Prefix {prec = app_prec; op = string "?"; arg = expr} 

            | PrimApp {op = pop; universals; arg} ->
                let op = prefix 4 1 (string "__" ^^ Primop.to_doc pop)
                    (surround_separate_map 4 0 empty
                        langle (comma ^^ break 1) rangle
                        Type.to_doc (Vector.to_list universals)) in
                Prefix {prec = app_prec; op; arg}

            | PrimBranch {op = bop; universals; arg; clauses} ->
                let op = prefix 4 1 (string "__" ^^ Branchop.to_doc bop)
                    (surround_separate_map 4 0 empty
                        (break 1 ^^ langle) (comma ^^ break 1) (rangle ^^ break 1)
                        (Type.to_doc) (Vector.to_list universals)) in
                let op = prefix 4 1 op (to_doc_prec app_prec arg) in
                Unary (prefix 4 1 op (surround_separate_map 0 1 (braces bar)
                    lbrace (break 1) rbrace
                    prim_clause_to_doc (Vector.to_list clauses)))

            | Pack {existentials; impl} ->
                let op = prefix 4 1 (string "pack") 
                    (surround_separate 4 0 empty
                        langle (comma ^^ break 1) rangle
                        (Vector1.to_list (Vector1.map Type.to_doc existentials))) in
                Prefix {prec = pack_prec; op; arg = impl}

            | Select {selectee; label} ->
                Postfix {prec = dot_prec; arg = selectee
                    ; op = dot ^^ string (Option.get (Name.basename label))}

            | Focus {focusee; index} ->
                Postfix {prec = dot_prec; arg = focusee
                    ; op = dot ^^ string (Int.to_string index)}

            | Fn {universals; param; body} ->
                Unary (string "fun"
                    ^^ surround_separate_map 4 0 empty
                            (blank 1 ^^ langle) (comma ^^ break 1) rangle
                            Type.def_to_doc (Vector.to_list universals)
                    ^^ blank 1 ^^ parens (def_to_doc param) ^^ blank 1
                    ^^ surround 4 1 lbrace (to_doc body) rbrace )

            | Let {defs; body} ->
                Unary (surround 4 1 (string "let" ^^ blank 1 ^^ lbrace)
                    (separate_map (semi ^^ hardline)
                        Stmt.to_doc (Array1.to_list defs)
                    ^^ semi ^^ hardline ^^ to_doc body)
                    rbrace)

            | Letrec {defs; body} ->
                Unary (surround 4 1 (string "letrec" ^^ blank 1 ^^ lbrace)
                    (separate_map (semi ^^ hardline)
                        Stmt.def_to_doc (Array1.to_list defs)
                    ^^ semi ^^ hardline ^^ to_doc body)
                    rbrace)

            | LetType {typedefs; body} ->
                Unary (surround 4 1 (string "lettype" ^^ blank 1 ^^ lbrace)
                    (separate_map (semi ^^ hardline)
                        Type.def_to_doc (Vector1.to_list typedefs)
                    ^^ semi ^^ hardline ^^ to_doc body)
                    rbrace)

            | Axiom {axioms; body} ->
                Unary (surround 4 1 (string "axiom" ^^ blank 1 ^^ lbrace)
                    (separate_map (semi ^^ hardline)
                        axiom_to_doc (Vector1.to_list axioms)
                    ^^ semi ^^ hardline ^^ to_doc body)
                    rbrace)

            | Unpack {existentials; var; value; body} ->
                Unary (surround 4 1 (string "unpack" ^^ blank 1 ^^ lbrace)
                    (infix 4 1 equals
                        (surround_separate_map 4 0 empty
                            langle (comma ^^ break 1) rangle
                            Type.def_to_doc (Vector1.to_list existentials)
                        ^^ blank 1 ^^ def_to_doc var)
                        (to_doc value)
                    ^^ semi ^^ hardline ^^ to_doc body)
                    rbrace)

            | Match {matchee; clauses} ->
                let start = string "match" ^^ blank 1 ^^ to_doc matchee ^^ blank 1 ^^ lbrace in
                Unary (surround_separate_map 0 1 (start ^^ rbrace)
                    start (break 1) rbrace
                    clause_to_doc (Vector.to_list clauses))

            | Record fields ->
                Unary (surround_separate_map 4 0 (braces empty)
                    lbrace (semi ^^ break 1) rbrace
                    (fun (label, field) ->
                        infix 4 1 equals (string (Option.get (Name.basename label)))
                            (to_doc field))
                    (Array.to_list fields))

            | Tuple exprs ->
                Unary (surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ break 1) rparen
                    to_doc (Array.to_list exprs))

            | Proxy typ -> Unary (brackets (Type.to_doc typ))

            | Use var -> Unary (var_to_doc var)
            | Const c -> Unary (Const.to_doc c) in
        to_doc_prec 0 expr

    and axiom_to_doc (name, universals, l, r) =
        let open PPrint in
        
        let universal_to_doc universals body =
            if Vector.length universals = 0
            then body
            else prefix 4 1
                (string "forall" ^^ blank 1 ^^
                    separate_map (blank 1) Type.kind_to_doc
                        (Vector.to_list universals))
                body in

        match Vector.to_list universals with
        | _ :: _ ->
            infix 4 1 colon (Name.to_doc name)
                (infix 4 1 tilde
                    (universal_to_doc universals (Type.to_doc l))
                    (universal_to_doc universals (Type.to_doc r)))
        | [] ->
            infix 4 1 colon (Name.to_doc name)
                (infix 4 1 tilde (Type.to_doc l) (Type.to_doc r))

    and clause_to_doc {pat; body} =
        PPrint.(bar ^^ blank 1
            ^^ infix 4 1 (string "->") (pat_to_doc pat) (to_doc body))

    and prim_clause_to_doc {res; prim_body} =
        PPrint.(bar ^^ blank 1
            ^^ infix 4 1 (string "->")
                (match res with
                | Some var -> def_to_doc var
                | None -> empty)
                (to_doc prim_body))

    and pat_to_doc (pat : pat) =
        let open PPrint in
        match pat.pterm with
        | TupleP pats ->
            surround_separate_map 4 0 (parens empty)
                lparen (comma ^^ break 1) rparen
                (pat_to_doc) (Vector.to_list pats)
        | ProxyP typ -> brackets (Type.to_doc typ)
        | VarP var -> parens (def_to_doc var)
        | WildP name -> underscore ^^ Name.to_doc name
        | ConstP c -> Const.to_doc c

    let var plicity name vtyp = {plicity; name; vtyp}

    let fresh_var plicity vtyp = var plicity (Name.fresh ()) vtyp

    let at pos typ term = {term; pos; typ; parent = None}

    let pat_at ppos ptyp pterm = {pterm; ppos; ptyp}

    let tuple vals = Tuple vals

    let focus focusee index = Focus {focusee; index}
    let fn universals param body = Fn {universals; param; body}
    let app callee universals arg = App {callee; universals; arg}
    let primapp op universals arg = PrimApp {op; universals; arg}
    let primbranch op universals arg clauses = PrimBranch {op; universals; arg; clauses}

    let let' defs body = match Array1.of_array defs with
        | Some defs -> (match body.term with
            | Let {defs = defs'; body} -> Let {defs = Array1.append defs defs'; body}
            | _ -> Let {defs; body})
        | None -> body.term

    let letrec defs body = match Array1.of_array defs with
        | Some defs -> (match body.term with
            | Letrec {defs = defs'; body} ->
                (* NOTE: expects alphatization, would be unsound otherwise: *)
                Letrec {defs = Array1.append defs defs'; body}
            | _ -> Letrec {defs; body})
        | None -> body.term

    let match' matchee clauses = Match {matchee; clauses}

    let axiom axioms body = match Vector1.of_vector axioms with
        | Some axioms -> Axiom {axioms; body}
        | None -> body.term

    let cast castee = function
        | Type.Refl _ -> castee.term
        | coercion -> Cast {castee; coercion}

    let pack existentials impl = match Vector1.of_vector existentials with
        | Some existentials -> Pack {existentials; impl}
        | None -> impl.term

    let unpack existentials var value body = Unpack {existentials; var; value; body}
    let record fields = Record fields

    let where base fields = match Array1.of_array fields with
        | Some fields -> Where {base; fields}
        | None -> base.term

    let select selectee label = Select {selectee; label}
    let proxy t = Proxy t
    let const c = Const c
    let use v = Use v
    let convert f expr = Convert (f, expr)

    let map_children f (expr : t) =
        let term = expr.term in
        let term' = match term with
            | Tuple vals ->
                let vals' = Array.map f vals in
                let noop = Stream.from (Source.zip_with (==)
                        (Source.array vals') (Source.array vals))
                    |> Stream.into (Sink.all ~where: Fun.id) in
                if noop then term else tuple vals'

            | Focus {focusee; index} ->
                let focusee' = f focusee in
                if focusee' == focusee then term else focus focusee' index

            | Fn {universals; param; body} ->
                let body' = f body in
                if body' == body then term else fn universals param body'

            | App {callee; universals; arg} ->
                let callee' = f callee in
                let arg' = f arg in
                if callee' == callee && arg' == arg
                then term
                else app callee' universals arg'

            | PrimApp {op; universals; arg} ->
                let arg' = f arg in
                if arg' == arg then term else primapp op universals arg'

            | PrimBranch {op; universals; arg; clauses} ->
                let arg' = f arg in
                let clauses' = clauses |> Vector.map (fun {res; prim_body} ->
                    {res; prim_body = f prim_body}) in
                if arg' == arg
                    && Stream.from (Source.zip_with (fun clause' clause ->
                            clause'.prim_body == clause.prim_body)
                        (Vector.to_source clauses') (Vector.to_source clauses))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then term
                else primbranch op universals arg' clauses'

            | Let {defs; body} ->
                let defs' = Array1.map (fun stmt -> match stmt with
                    | Stmt.Def (pos, var, expr) ->
                        let expr' = f expr in
                        if expr' == expr then stmt else Def (pos, var, expr')
                    | Expr expr ->
                        let expr' = f expr in
                        if expr' == expr then stmt else Expr expr'
                ) defs in
                let body' = f body in
                if body' == body
                    && Stream.from (Source.zip_with (==)
                        (Array1.to_source defs') (Array1.to_source defs))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then term
                else let' (Array1.to_array defs') body'

            | Letrec {defs; body} ->
                let defs' = Array1.map (fun ((pos, var, expr) as def) ->
                    let expr' = f expr in
                    if expr' == expr then def else (pos, var, expr')
                ) defs in
                let body' = f body in
                if body' == body
                    && Stream.from (Source.zip_with (==)
                        (Array1.to_source defs') (Array1.to_source defs))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then term
                else letrec (Array1.to_array defs') body'

            | LetType {typedefs; body} ->
                let body' = f body in
                if body' == body then term else LetType {typedefs; body = body'}

            | Axiom {axioms; body} ->
                let body' = f body in
                if body' == body then term else Axiom {axioms; body = body'}

            | Cast {castee; coercion} ->
                let castee' = f castee in
                if castee' == castee then term else cast castee' coercion

            | Pack {existentials; impl} ->
                let impl' = f impl in
                if impl' == impl then term else pack (Vector1.to_vector existentials) impl'

            | Unpack {existentials; var; value; body} ->
                let value' = f value in
                let body' = f body in
                if value' == value && body' == body
                then term
                else unpack existentials var value' body'

            | Record fields ->
                let fields' = Array.map (fun (label, field) -> (label, f field)) fields in
                let noop = Stream.from (Source.zip_with (fun (_, expr') (_, expr) -> expr' == expr)
                        (Source.array fields') (Source.array fields))
                    |> Stream.into (Sink.all ~where: Fun.id) in
                if noop then term else record fields'

            | With {base; label; field} ->
                let base' = f base in
                let field' = f field in
                if base' == base && field' == field then term else With {base = base'; label; field = field'}

            | Where {base; fields} ->
                let base' = f base in
                let fields' = Array1.map (fun (label, field) -> (label, f field)) fields in
                if base' == base
                    && Stream.from (Source.zip_with (fun (_, expr') (_, expr) -> expr' == expr)
                        (Array1.to_source fields') (Array1.to_source fields))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then term
                else where base' (Array1.to_array fields')

            | Select {selectee; label} ->
                let selectee' = f selectee in
                if selectee' == selectee then term else select selectee' label

            | Match {matchee; clauses} ->
                let matchee' = f matchee in
                let clauses' = Vector.map (fun {pat; body} -> {pat; body = f body}) clauses in
                if matchee' == matchee
                    && Stream.from (Source.zip_with (fun clause' clause -> clause'.body == clause.body)
                        (Vector.to_source clauses') (Vector.to_source clauses))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then term
                else match' matchee' clauses'

            | Proxy _ | Use _ | Const _ -> term

            | Convert (co, expr) ->
                let expr' = f expr in
                if expr' == expr then term else convert co expr' in
        if term' == term then expr else {expr with term = term'}

    let map_pat_children f (pat : pat) =
        let term = pat.pterm in
        let term' = match term with
            | TupleP pats ->
                let pats' = Vector.map f pats in
                if Stream.from (Source.zip_with (fun pat pat' -> pat == pat')
                        (Vector.to_source pats) (Vector.to_source pats'))
                    |> Stream.into (Sink.all ~where: Fun.id)
                then term
                else TupleP pats'

            | ProxyP _ | ConstP _ | VarP _ | WildP _ -> term in
        if term' == term then pat else {pat with pterm = term'}

    module Var = struct
        type t = var

        let compare (var : var) (var' : var) = Name.compare var.name var'.name
    end

    module VarSet = Set.Make(Var)
end

and Coercer : FcSigs.COERCER with type expr = Expr.t = struct
    type expr = Expr.t

    type t = expr -> expr

    let id = Fun.id

    let coercer = Fun.id

    let apply f (expr : Expr.t) = match expr.term with
        | Use _ | Const _ -> f expr
        | _ ->
            let {Expr.term = _; pos; typ; parent = _} = expr in
            let var = Expr.fresh_var Explicit typ in
            let pat = Expr.pat_at pos typ (VarP var) in
            let body = f (Expr.at pos typ (Expr.use var)) in
            Expr.at pos typ (Expr.let' [|Def (pos, pat, expr)|] body)

    let apply_opt f expr = match f with
        | Some f -> apply f expr
        | None -> expr
end

and Stmt : FcSigs.STMT
    with type expr = Expr.t
    with type pat = Expr.pat
= struct
    module Type = Type

    type expr = Expr.t
    type pat = Expr.pat

    type def = Util.span * pat * expr

    type t
        = Def of def
        | Expr of expr

    let def_to_doc ((_, var, expr) : def) =
        PPrint.(infix 4 1 equals (Expr.pat_to_doc var) (Expr.to_doc expr))

    let to_doc = function
        | Def def -> def_to_doc def
        | Expr expr -> Expr.to_doc expr

    let rhs (Def (_, _, expr) | Expr expr) = expr
end

