module Type = SyntacticType

module rec Expr : (SimpleFcSigs.EXPR
    with type stmt = Stmt.t
    with type decl = Stmt.decl
) = struct
    module Type = Type

    type typ = Type.t
    type kind = Type.kind
    type stmt = Stmt.t
    type decl = Stmt.decl

    type def = Name.t * typ

    type t =
        { term : t'
        ; mutable parent : t option
        ; typ : typ
        ; pos : Util.span }

    and t' =
        | Use of Name.t

        | Fn of {universals : (Name.t * kind) Vector.t
            ; param : Name.t * typ; mutable body : t}
        | App of {mutable callee : t; universals : typ Vector.t
            ; mutable arg : t}
        | PrimApp of {op : Primop.t; universals : typ Vector.t
            ; mutable arg : t}
        | PrimBranch of {op : Branchop.t; universals : typ Vector.t
            ; mutable arg : t; clauses : prim_clause Vector.t}

        | Let of {decls : stmt Array1.t; mutable body : t}
        | Letrec of {decls : Stmt.decl Array1.t; mutable body : t}
        | Match of {mutable matchee : t; clauses : clause Vector.t}

        (*| Axiom of { axioms : (Name.t * Type.kind Vector.t * typ * typ) Vector1.t
            ; mutable body : t }*)
        | Cast of {mutable castee : t; coercion : Type.coercion}

        | Record of (Name.t * t) array
        | Where of {mutable base : t; fields : (Name.t * t) Array1.t}
        | With of {mutable base : t; label : Name.t; mutable field : t}
        | Select of {mutable selectee : t; label : Name.t}
        | Tuple of t array
        | Focus of {mutable focusee : t; index : int}

        | Proxy of typ
        | Const of Const.t

    and clause = {pat : pat; mutable body : t}
    and prim_clause = {res : Name.t option; prim_body : t}

    and pat = {pterm: pat'; ptyp : typ; ppos : Util.span}
    and pat' =
        | ProxyP of typ
        | ConstP of Const.t
        | VarP of Name.t
        | WildP of Name.t

(* --- *)

    let cast_prec = 0
    let app_prec = cast_prec + 1
    let dot_prec = app_prec + 1

    let prec_parens parenthesize doc = if parenthesize then PPrint.parens doc else doc

    let def_to_doc (name, t) = PPrint.(infix 4 1 colon (Name.to_doc name) (Type.to_doc t))

    let rec to_doc (expr : t) =
        let open PPrint in

        let rec to_doc_prec prec expr = match expr.term with
            | Fn {universals; param; body} ->
                string "fun"
                ^^ surround_separate_map 4 0 empty
                    (blank 1 ^^ langle) (comma ^^ break 1) rangle
                    Type.def_to_doc (Vector.to_list universals)
                ^^ blank 1 ^^ parens (def_to_doc param) ^^ blank 1
                ^^ surround 4 1 lbrace (to_doc body) rbrace 

            | App {callee; universals; arg} ->
                prefix 4 1
                    (prefix 4 0 (to_doc_prec app_prec callee)
                        (surround_separate_map 4 0 empty
                            (blank 1 ^^ langle) (comma ^^ break 1) rangle
                            Type.to_doc (Vector.to_list universals)))
                    (to_doc_prec (app_prec + 1) arg)
                |> prec_parens (prec > app_prec)

            | PrimApp {op; universals; arg} ->
                prefix 4 1
                    (prefix 4 0 (string "__" ^^ Primop.to_doc op)
                        (surround_separate_map 4 0 empty
                            (blank 1 ^^ langle) (comma ^^ break 1) rangle
                            Type.to_doc (Vector.to_list universals)))
                    (to_doc_prec (app_prec + 1) arg)
                |> prec_parens (prec > app_prec)

            | PrimBranch {op; universals; arg; clauses} ->
                prefix 4 1
                    (prefix 4 0 (string "__" ^^ Branchop.to_doc op)
                        (surround_separate_map 4 0 empty
                            (blank 1 ^^ langle) (comma ^^ break 1) rangle
                            Type.to_doc (Vector.to_list universals)))
                    (to_doc_prec (app_prec + 1) arg
                    ^^ blank 1 ^^ surround_separate_map 0 1 (braces bar)
                        lbrace (break 1) rbrace
                        prim_clause_to_doc (Vector.to_list clauses))
                |> prec_parens (prec > app_prec)

            | Let {decls; body} ->
                surround 4 1 (string "let" ^^ blank 1 ^^ lbrace)
                    (separate_map (semi ^^ hardline)
                        Stmt.to_doc (Array1.to_list decls)
                    ^^ semi ^^ hardline ^^ to_doc body)
                    rbrace

            | Letrec {decls; body} ->
                surround 4 1 (string "letrec" ^^ blank 1 ^^ lbrace)
                    (separate_map (semi ^^ hardline)
                        Stmt.decl_to_doc (Array1.to_list decls)
                    ^^ semi ^^ hardline ^^ to_doc body)
                    rbrace
            
            | Match {matchee; clauses} ->
                let start = string "match" ^^ blank 1
                    ^^ to_doc matchee ^^ blank 1 ^^ lbrace in
                surround_separate_map 0 1 (start ^^ rbrace)
                    start (break 1) rbrace
                    clause_to_doc (Vector.to_list clauses)

            (*| Axiom {axioms; body} ->
                group(
                    surround 4 1 (string "axiom")
                        (align (separate_map (semi ^^ break 1) (axiom_to_doc s)
                            (Vector1.to_list axioms)))
                        (string "in")
                    ^/^ to_doc s body)*)

            | Cast {castee; coercion} ->
                infix 4 1 (string "|>") (to_doc_prec cast_prec castee)
                    (Type.coercion_to_doc coercion)
                |> prec_parens (prec > cast_prec)
            
            | Record fields ->
                surround_separate_map 4 0 (braces empty)
                    lbrace (comma ^^ break 1) rbrace
                    (fun (label, field) ->
                        infix 4 1 equals (string (Name.basename label |> Option.get))
                            (to_doc field))
                    (Array.to_list fields)

            | Where {base; fields} ->
                surround 4 0 (to_doc base ^^ blank 1 ^^ string "where" ^^ blank 1 ^^ lbrace)
                    (separate_map (comma ^^ break 1) 
                        (fun (label, field) ->
                            infix 4 1 equals (Name.to_doc label) (to_doc field))
                        (Array1.to_list fields))
                    rbrace
                |> prec_parens (prec > 0)

            | With {base; label; field} ->
                infix 4 1 (string "with") (to_doc base)
                    (infix 4 1 equals (Name.to_doc label) (to_doc field))
                |> prec_parens (prec > 0)

            | Select {selectee; label} ->
                prefix 4 0 (to_doc_prec dot_prec selectee)
                    (dot ^^ string (Option.get (Name.basename label)))

            | Tuple exprs ->
                surround_separate_map 4 0 (parens empty)
                    lparen (comma ^^ break 1) rparen
                    to_doc (Array.to_list exprs)

            | Focus {focusee; index} ->
                prefix 4 1 (to_doc_prec dot_prec focusee)
                    (dot ^^ string (Int.to_string index))

            | Proxy typ -> brackets (Type.to_doc typ)
            | Use var -> Name.to_doc var
            | Const c -> Const.to_doc c in

        to_doc_prec 0 expr


    and clause_to_doc {pat; body} =
        PPrint.(bar ^^ blank 1
            ^^ infix 4 1 (string "->") (pat_to_doc pat) (to_doc body))

    and prim_clause_to_doc {res; prim_body} =
        PPrint.(bar ^^ blank 1
            ^^ infix 4 1 (string "->")
                (match res with
                | Some name -> Name.to_doc name
                | None -> empty)
                (to_doc prim_body))

    and pat_to_doc (pat : pat) =
        let open PPrint in
        match pat.pterm with
        | ProxyP typ -> brackets (Type.to_doc typ)
        | VarP var -> Name.to_doc var
        | WildP name -> underscore ^^ Name.to_doc name
        | ConstP c -> Const.to_doc c


(* --- *)

    let at pos typ term = {term; pos; typ; parent = None}

    let fn universals param body = Fn {universals; param; body}
    let app callee universals arg = App {callee; universals; arg}
    let primapp op universals arg = PrimApp {op; universals; arg}
    let primbranch op universals arg clauses = PrimBranch {op; universals; arg; clauses}

    let let' decls body = match Array1.of_array decls with
        | Some decls -> (match body.term with
            | Let {decls = decls'; body} -> Let {decls = Array1.append decls decls'; body}
            | _ -> Let {decls; body})
        | None -> body.term

    let letrec decls body = match Array1.of_array decls with
        | Some decls -> (match body.term with
            | Letrec {decls = decls'; body} ->
                (* NOTE: expects alphatization, would be unsound otherwise: *)
                Letrec {decls = Array1.append decls decls'; body}
            | _ -> Letrec {decls; body})
        | None -> body.term

    let match' matchee clauses = Match {matchee; clauses}

(*
    let axiom axioms body = match Vector1.of_vector axioms with
        | Some axioms -> Axiom {axioms; body}
        | None -> body.term
*)
    let cast castee = function
        (*| Refl _ -> castee.term*)
        | coercion -> Cast {castee; coercion}

    let record fields = Record fields

    let where base fields = match Array1.of_array fields with
        | Some fields -> Where {base; fields}
        | None -> base.term

    let with' base label field = With {base; label; field}

    let select selectee label = Select {selectee; label}

    let tuple vals = Tuple vals

    let focus focusee index = Focus {focusee; index}

    let proxy t = Proxy t
    let const c = Const c
    let use v = Use v
end

and Stmt : (SimpleFcSigs.STMT
    with type expr = Expr.t
) = struct
    module Type = Type

    type expr = Expr.t

    type decl = Util.span * Name.t * Type.t * expr

    type t
        = Decl of decl
        | Expr of expr

    let decl_to_doc ((_, name, t, expr) : decl) =
        PPrint.(infix 4 1 equals
            (Expr.def_to_doc (name, t))
            (Expr.to_doc expr))

    let to_doc = function
        | Decl decl -> decl_to_doc decl
        | Expr expr -> Expr.to_doc expr
end

module Program = struct
    type kind = Type.kind

    type t =
        { type_fns : (Name.t * kind) Vector.t
        ; decls : Stmt.decl Vector.t
        ; main : Expr.t }

    let to_doc {type_fns; decls; main} =
        let open PPrint in
        separate_map (twice hardline) Type.def_to_doc (Vector.to_list type_fns)
        ^/^ separate_map (twice hardline) (fun def -> Stmt.decl_to_doc def ^^ semi)
            (Vector.to_list decls)
        ^^ twice (twice hardline) ^^ Expr.to_doc main
end

