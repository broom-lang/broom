open Asserts

module PP = PPrint


type 'a with_pos = 'a Util.with_pos

module rec Term : AstSigs.TERM with type Expr.typ = Type.t = struct
    module Expr = struct
        module Stmt = Term.Stmt

        type typ = Type.t
        type stmt = Stmt.t
        type def = Stmt.def

        type t =
            | Tuple of t with_pos Vector.t
            | Focus of t with_pos * int
            | Ann of t with_pos * typ with_pos
            | Fn of Util.plicity * clause Vector.t
            | App of t with_pos * Util.plicity * t with_pos
            | AppSequence of t with_pos Vector1.t
            | PrimApp of Primop.t * t with_pos option * t with_pos
            | PrimBranch of Branchop.t * t with_pos option * t with_pos * clause Vector.t
            | Let of def Vector1.t * t with_pos
            | Record of stmt Vector.t
            | Select of t with_pos * Name.t
            | Proxy of typ
            | Var of Name.t
            | Wild of Name.t
            | Const of Const.t

        and clause = {params : pat with_pos; body : t with_pos}

        and pat = t

        (*
        (* FIXME: Printing syntax differs from parsed syntax, so use Grammar: *)

        let tuple = PIso.prism (fun exprs -> Tuple exprs) (function
            | Tuple exprs -> Some exprs
            | _ -> None)

        let focus = PIso.prism (fun (tup, i) -> Focus (tup, i)) (function
            | Focus (tup, i) -> Some (tup, i)
            | _ -> None)

        let ann = PIso.prism (fun (expr, typ) -> Ann (expr, typ)) (function
            | Ann (expr, typ) -> Some (expr, typ)
            | _ -> None)

        let fn = PIso.prism (fun (param, body) -> Fn (param, body)) (function
            | Fn (param, body) -> Some (param, body)
            | _ -> None)

        let app = PIso.prism (fun (callee, plicity, arg) -> App (callee, plicity, arg)) (function
            | App (callee, plicity, arg) -> Some (callee, plicity, arg)
            | _ -> None)

        let app_seq = PIso.prism (fun exprs -> AppSequence exprs) (function
            | AppSequence exprs -> Some exprs
            | _ -> None)

        let primapp = PIso.prism (fun (op, iarg, arg) -> PrimApp (op, iarg, arg)) (function
            | PrimApp (op, iarg, arg) -> Some (op, iarg, arg)
            | _ -> None)

        let primbranch = PIso.prism (fun (op, iarg, arg, clauses) -> PrimBranch (op, iarg, arg, clauses))
            (function
            | PrimBranch (op, iarg, arg, clauses) -> Some (op, iarg, arg, clauses)
            | _ -> None)

        let let' = PIso.prism (fun (defs, body) -> Let (defs, body)) (function
            | Let (defs, body) -> Some (defs, body)
            | _ -> None)

        let record = PIso.prism (fun stmts -> Record stmts) (function
            | Record stmts -> Some stmts
            | _ -> None)

        let select = PIso.prism (fun (r, label) -> Select (r, label)) (function
            | Select (r, label) -> Some (r, label)
            | _ -> None)

        let proxy = PIso.prism (fun typ -> Proxy typ) (function
            | Proxy typ -> Some typ
            | _ -> None)

        let var = PIso.prism (fun var -> Var var) (function
            | Var var -> Some var
            | _ -> None)

        let wild = PIso.prism (fun name -> Wild name) (function
            | Wild name -> Some name
            | _ -> None)

        let const = PIso.prism (fun c -> Const c) (function
            | Const c -> Some c
            | _ -> None)

        let positioned = PIso.iso (fun _ -> Asserts.todo None)
            (fun {Util.v; pos = _} -> v)

        let grammar =
            let open Grammar in let open Grammar.Infix in

            fix (fun expr ->
                let atom = positioned <$> (var <$> Name.grammar
                    <|> (wild <$> (token '_' *> Name.grammar))
                    <|> (const <$> Const.grammar)) in

                let tuple = surround_separate 4 0 (parens (pure Vector.empty))
                    lparen (comma *> break 1) rparen expr
                    |> map tuple in

                let surrounded = positioned <$> tuple in

                let nestable = surrounded <|> atom in

                let access =
                    let adapt = PIso.iso (function
                            | (focusee, Some is) -> (focusee, is)
                            | (focusee, None) -> (focusee, []))
                        (function
                        | (focusee, []) -> (focusee, None)
                        | (focusee, is) -> (focusee, Some is)) in
                    let f = PIso.comp (PIso.fold_left (PIso.comp positioned focus)) adapt in
                    f <$> (nestable <*> opt (break 1 *> (many1 (dot *> break 1 *> int)))) in

                let app =
                    let adapt = PIso.iso (fun _ -> todo None) (function
                        | (callee, Util.Explicit, arg) -> (match callee.Util.v with
                            | App (callee, Implicit, iarg) -> ((callee, [arg]), Some [iarg])
                            | _ -> ((callee, [arg]), None))
                        | (callee, Implicit, iarg) -> ((callee, [iarg]), Some [])) in
                    PIso.comp positioned (PIso.comp app adapt)
                        <$> (access <*> many (break 1 *> access)
                            <*> opt (break 1 *> token '@' *> many (break 1 *> access))) in

                app)*)

        let colon_prec = 1
        let app_prec = 9
        let dot_prec = 10

        let prec_parens show_parens doc = if show_parens then PP.parens doc else doc

        let rec to_doc (expr : t with_pos) =
            let open PPrint in
            let rec to_doc prec (expr : t with_pos) = match expr.v with
                | Proxy typ -> Type.to_doc {expr with v = typ}

                | Ann (expr, typ) ->
                    infix 4 1 colon (to_doc (colon_prec + 1) expr) (Type.to_doc typ)
                    |> prec_parens (prec > colon_prec)

                | App (callee, Explicit, args) ->
                    prefix 4 1 (to_doc (app_prec + 1) callee) (to_doc (app_prec + 1) args)
                    |> prec_parens (prec > app_prec)
                | App (callee, Implicit, args) ->
                    prefix 4 1 (to_doc (app_prec + 1) callee)
                        (to_doc (app_prec + 1) args ^^ blank 1 ^^ string "@")
                    |> prec_parens (prec > app_prec)
                | AppSequence exprs ->
                    separate_map (break 1) (to_doc (app_prec + 1)) (Vector1.to_list exprs)
                    |> prec_parens (prec > app_prec)
                | PrimApp (op, Some iargs, args) ->
                    infix 4 1 (string "@")
                        (prefix 4 1 (string "__" ^^ Primop.to_doc op) (to_doc (app_prec + 1) iargs))
                        (to_doc (app_prec + 1) args)
                    |> prec_parens (prec > app_prec)
                | PrimApp (op, None, args) ->
                    prefix 4 1 (string "__" ^^ Primop.to_doc op) (to_doc (app_prec + 1) args)
                    |> prec_parens (prec > app_prec)
                | PrimBranch (op, Some iargs, args, clauses) ->
                    infix 4 1 (string "@")
                        (prefix 4 1 (string "__" ^^ Branchop.to_doc op)
                         (to_doc (app_prec + 1) args))
                        ((to_doc (app_prec + 1) iargs) ^^ blank 1
                         ^^ to_doc (app_prec + 1) {expr with v = Fn (Explicit, clauses)})
                    |> prec_parens (prec > app_prec)
                | PrimBranch (op, None, args, clauses) ->
                    prefix 4 1 (string "__" ^^ Branchop.to_doc op)
                        ((to_doc (app_prec + 1) args) ^^ blank 1
                        ^^ to_doc (app_prec + 1) {expr with v = Fn (Explicit, clauses)})
                    |> prec_parens (prec > app_prec)
                | Let (defs, body) ->
                    string "__let" ^^ blank 1
                    ^^ surround_separate 4 0 (braces empty)
                        lbrace (semi ^^ break 1) rbrace
                        (Vector1.to_list (Vector1.map Stmt.def_to_doc defs)
                        @ [to_doc 0 body])
                    |> prec_parens (prec > app_prec)

                | Focus (focusee, i) ->
                    prefix 4 0 (to_doc (dot_prec + 1) focusee) (dot ^^ string (Int.to_string i))
                    |> prec_parens (prec > dot_prec) 
                | Select (selectee, label) ->
                    prefix 4 0 (to_doc (dot_prec + 1) selectee)
                        (dot ^^ string (Option.get (Name.basename label)))
                    |> prec_parens (prec > dot_prec) 

                | Tuple exprs ->
                    surround_separate_map 4 0 (parens empty) lparen (comma ^^ break 1) rparen
                        (to_doc 0) (Vector.to_list exprs)
                | Record stmts ->
                    surround_separate_map 4 0 (braces empty) lbrace (semi ^^ break 1) rbrace
                        Stmt.to_doc (Vector.to_list stmts)
                | Fn (plicity, clauses) ->
                    surround_separate_map 4 0 (braces bar) lbrace (break 1) rbrace
                        (clause_to_doc (Util.plicity_arrow plicity))
                        (Vector.to_list clauses)
                | Var name -> Name.to_doc name
                | Wild name -> underscore ^^ Name.to_doc name
                | Const v -> Const.to_doc v in
            to_doc 0 expr

        and clause_to_doc arrow {params; body} =
            PPrint.(infix 4 1 arrow (bar ^^ blank 1 ^^ to_doc params) (to_doc body))
    end

    module Stmt = struct
        type expr = Expr.t
        type pat = Expr.pat

        type def = Util.span * pat with_pos * expr with_pos

        type t =
            | Def of def
            | Expr of expr with_pos

        let pos = function
            | Def (pos, _, _) -> pos
            | Expr expr -> expr.pos

        let def_to_doc ((_, pat, expr) : def) =
            PP.infix 4 1 PP.equals (Expr.to_doc pat) (Expr.to_doc expr)

        let to_doc = function
            | Def def -> def_to_doc def
            | Expr expr -> Expr.to_doc expr
    end
end

and Type : AstSigs.TYPE
    with type expr = Term.Expr.t
    with type pat = Term.Expr.pat
    with type def = Term.Stmt.def
= struct
    type expr = Term.Expr.t
    type pat = Term.Expr.pat
    type def = Term.Stmt.def

    type t =
        | Tuple of t with_pos Vector.t
        | Pi of {domain : pat with_pos; eff : t with_pos option; codomain : t with_pos}
        | Impli of {domain : pat with_pos; codomain : t with_pos}
        | Declare of decl Vector1.t * t with_pos
        | Record of decl Vector.t
        | Row of decl Vector.t
        | Path of expr
        | Prim of Prim.t

    and decl =
        | Def of def
        | Decl of Util.span * pat with_pos * t with_pos

    let rec to_doc (typ : t with_pos) =
        let open PPrint in
        match typ.v with
        | Tuple typs ->
            surround_separate_map 4 0 (parens colon)
                (lparen ^^ colon) (comma ^^ break 1) rparen
                to_doc (Vector.to_list typs)
        | Pi {domain; eff; codomain} ->
            prefix 4 1 (Term.Expr.to_doc domain)
                (let codoc = string "->" ^^ blank 1 ^^ to_doc codomain in
                match eff with
                | Some eff -> prefix 4 1 (string "-!" ^^ blank 1 ^^ to_doc eff) codoc
                | None -> codoc)
        | Impli {domain; codomain} ->
            prefix 4 1 (Term.Expr.to_doc domain ^^ blank 1)
                (string "=>" ^^ to_doc codomain)
        | Declare (decls, body) ->
            string "__declare" ^^ blank 1
            ^^ surround_separate 4 0 (braces empty)
                lbrace (semi ^^ break 1) rbrace
                (Vector1.to_list (Vector1.map decl_to_doc decls)
                @ [to_doc body])

        | Record stmts ->
            surround_separate_map 4 0 (braces colon)
                (lbrace ^^ colon) (semi ^^ break 1) rbrace
                decl_to_doc (Vector.to_list stmts)
        | Row stmts ->
            surround_separate_map 4 0 (parens bar)
                (lparen ^^ bar) (break 1 ^^ bar ^^ break 1) rparen
                decl_to_doc (Vector.to_list stmts)
        | Path expr -> Term.Expr.to_doc {typ with v = expr}
        | Prim pt -> Prim.to_doc pt

    and decl_to_doc = function
        | Def def -> Term.Stmt.def_to_doc def
        | Decl (_, pat, typ) ->
            PPrint.(infix 4 1 colon (Term.Expr.to_doc pat) (to_doc typ))

    module Decl = struct
        type t = decl

        let to_doc = decl_to_doc

        let pos = function
            | Def (pos, _, _) -> pos
            | Decl (pos, _, _) -> pos
    end
end

