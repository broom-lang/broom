module PP = PPrint

type span = Util.span
type 'a with_pos = 'a Util.with_pos

module Primop = struct
    type t =
        | Include | Require
        | Do | Let | Module | Interface
        | Explicitly

        | Pair | Fst | Snd
        | CellNew | CellInit | CellGet
        | Int | String | Type
        | TypeOf
        | Import
        | GlobalSet | GlobalGet

        | IAdd | ISub | IMul | IDiv
        | ILt | ILe | IGt | IGe | IEq

    let grammar =
        let open Grammar in let open Grammar.Infix in
        text "include" *> pure Include
        <|> text "require" *> pure Require
        <|> text "do" *> pure Do
        <|> text "let" *> pure Let
        <|> text "module" *> pure Module
        <|> text "interface" *> pure Interface
        <|> text "explicitly" *> pure Explicitly

        <|> text "pair" *> pure Pair
        <|> text "fst" *> pure Fst
        <|> text "snd" *> pure Snd
        <|> text "cellNew" *> pure CellNew
        <|> text "cellInit" *> pure CellInit
        <|> text "cellGet" *> pure CellGet
        <|> text "int" *> pure Int
        <|> text "string" *> pure String
        <|> text "type" *> pure Type
        <|> text "typeof" *> pure TypeOf
        <|> text "import" *> pure Import
        <|> text "globalSet" *> pure GlobalSet
        <|> text "globalGet" *> pure GlobalGet

        <|> text "iadd" *> pure IAdd
        <|> text "isub" *> pure ISub
        <|> text "imul" *> pure IMul
        <|> text "idiv" *> pure IDiv
        <|> text "ilt" *> pure ILt
        <|> text "ile" *> pure ILe
        <|> text "igt" *> pure IGt
        <|> text "ige" *> pure IGe
        <|> text "ieq" *> pure IEq

    let to_doc = PPrinter.of_grammar grammar

    let of_string = function
        | "include" -> Some Include
        | "require" -> Some Require
        | "do" -> Some Do
        | "let" -> Some Let
        | "module" -> Some Module
        | "interface" -> Some Interface
        | "explicitly" -> Some Explicitly

        | "pair" -> Some Pair
        | "fst" -> Some Fst
        | "snd" -> Some Snd
        | "cellNew" -> Some CellNew
        | "cellInit" -> Some CellInit
        | "cellGet" -> Some CellGet
        | "int" -> Some Int
        | "string" -> Some String
        | "type" -> Some Type
        | "typeof" -> Some TypeOf
        | "import" -> Some Import
        | "globalSet" -> Some GlobalSet
        | "globalGet" -> Some GlobalGet

        | "iadd" -> Some IAdd
        | "isub" -> Some ISub
        | "imul" -> Some IMul
        | "idiv" -> Some IDiv
        | "ilt" -> Some ILt
        | "ile" -> Some ILe
        | "igt" -> Some IGt
        | "ige" -> Some IGe
        | "ieq" -> Some IEq

        | _ -> None
end

module rec Expr : (AstSigs.EXPR
    with type primop = Primop.t
    with type stmt = Stmt.t
    with type decl = Decl.t)
= struct
    type primop = Primop.t
    type stmt = Stmt.t
    type decl = Decl.t

    type t' =
        | Fn of clause Vector.t
        | ImpliFn of clause Vector.t
        | App of t Vector.t
        | PrimApp of primop * t Vector.t
        | PiT of {domain : t; eff : t option; codomain : t}
        | ImpliT of {domain : t; codomain : t}

        | Ann of t * t

        | Tuple of t Vector.t
        | Focus of t * int
        | TupleT of t Vector.t

        | Record of stmt Vector.t
        | Select of t * Name.t
        | RecordT of decl Vector.t

        | VariantT of decl Vector.t

        | RowT of decl Vector.t

        | Var of Name.t
        | Wild of Name.t
        | Const of Const.t
        | PrimT of Prim.t

    and t = t' with_pos

    and clause = {params : t; body : t}

    let colon_prec = 1
    let app_prec = 2
    let dot_prec = 3

    let prec_parens show_parens doc = if show_parens then PP.parens doc else doc

    let rec to_doc (expr : t) =
        let open PPrint in
        let rec to_doc prec (expr : t) = match expr.v with
            | Ann (expr, typ) ->
                infix 4 1 colon (to_doc (colon_prec + 1) expr) (to_doc 0 typ)
                |> prec_parens (prec > colon_prec)

            | App exprs ->
                separate_map (break 1) (to_doc (app_prec + 1)) (Vector.to_list exprs)
                |> prec_parens (prec > app_prec)
            | PrimApp (op, args) ->
                prefix 4 1 (string "__" ^^ Primop.to_doc op)
                    (separate_map (break 1) (to_doc (app_prec + 1))
                        (Vector.to_list args))
                |> prec_parens (prec > app_prec)
           
            | Focus (focusee, i) ->
                prefix 4 0 (to_doc (dot_prec + 1) focusee) (dot ^^ string (Int.to_string i))
                |> prec_parens (prec > dot_prec) 
            | Select (selectee, label) ->
                prefix 4 0 (to_doc (dot_prec + 1) selectee)
                    (dot ^^ string (Option.get (Name.basename label)))
                |> prec_parens (prec > dot_prec) 

            | Fn clauses ->
                surround_separate_map 4 0 (braces bar) lbrace (break 1) rbrace
                    (clause_to_doc (string "->"))
                    (Vector.to_list clauses)
            | ImpliFn clauses ->
                surround_separate_map 4 0 (braces bar) lbrace (break 1) rbrace
                    (clause_to_doc (string "=>"))
                    (Vector.to_list clauses)
            | PiT {domain; eff; codomain} ->
                surround 4 1 lbracket
                    (prefix 4 1 (Expr.to_doc domain)
                        (let codoc = string "->" ^^ blank 1 ^^ to_doc 0 codomain in
                        match eff with
                        | Some eff -> prefix 4 1 (string "-!" ^^ blank 1 ^^ to_doc 0 eff) codoc
                        | None -> codoc))
                    rbracket
            | ImpliT {domain; codomain} ->
                prefix 4 1 (Expr.to_doc domain ^^ blank 1)
                    (string "=>" ^^ to_doc 0 codomain)

            | Tuple exprs ->
                surround_separate_map 4 0 (parens empty) lparen (comma ^^ break 1) rparen
                    (to_doc 0) (Vector.to_list exprs)
            | TupleT typs ->
                surround_separate_map 4 0 (parens colon)
                    (lparen ^^ colon) (comma ^^ break 1) rparen
                    (to_doc 0) (Vector.to_list typs)

            | Record stmts ->
                surround_separate_map 4 0 (braces empty) lbrace (semi ^^ break 1) rbrace
                    Stmt.to_doc (Vector.to_list stmts)
            | RecordT decls ->
                surround_separate_map 4 0 (braces colon)
                    (lbrace ^^ colon) (semi ^^ break 1) rbrace
                    Decl.to_doc (Vector.to_list decls)

            | VariantT decls ->
                surround_separate_map 4 0 (braces sharp)
                    (lbrace ^^ sharp) (semi ^^ break 1) rbrace
                    Decl.to_doc (Vector.to_list decls)

            | RowT decls ->
                surround_separate_map 4 0 (parens bar)
                    (lparen ^^ bar) (semi ^^ break 1) rparen
                    Decl.to_doc (Vector.to_list decls)

            | Var name -> Name.to_doc name
            | Wild name -> underscore ^^ Name.to_doc name
            | Const v -> Const.to_doc v
            | PrimT p -> string "__" ^^ Prim.to_doc p in
        to_doc 0 expr

    and clause_to_doc arrow {params; body} =
        PPrint.(infix 4 1 arrow (bar ^^ blank 1 ^^ to_doc params) (to_doc body))

    let map_clause_exprs f ({params; body} as clause) =
        let params' = f params in
        let body' = f body in
        if params' == params && body' == body then clause else {params = params'; body = body'}

    let map_children f (expr : t) =
        let term = expr.v in
        let term' = match term with
            | Fn clauses ->
                let clauses' = Vector.map_children (map_clause_exprs f) clauses in
                if clauses' == clauses then term else Fn clauses'

            | ImpliFn clauses ->
                let clauses' = Vector.map_children (map_clause_exprs f) clauses in
                if clauses' == clauses then term else ImpliFn clauses'

            | App exprs ->
                let exprs' = Vector.map_children f exprs in
                if exprs' == exprs then term else App exprs'

            | PrimApp (op, exprs) ->
                let exprs' = Vector.map_children f exprs in
                if exprs' == exprs then term else PrimApp (op, exprs')

            | PiT {domain; eff; codomain} ->
                let domain' = f domain in
                let eff' = Option.map f eff in
                let codomain' = f codomain in
                if domain' == domain && eff' == eff && codomain' == codomain
                then term
                else PiT {domain = domain'; eff = eff'; codomain = codomain'}

            | ImpliT {domain; codomain} ->
                let domain' = f domain in
                let codomain' = f codomain in
                if domain' == domain && codomain' == codomain
                then term
                else ImpliT {domain = domain'; codomain = codomain'}

            | Ann (expr, typ) ->
                let expr' = f expr in
                let typ' = f typ in
                if expr' == expr && typ' == typ then term else Ann (expr', typ')

            | Tuple exprs ->
                let exprs' = Vector.map_children f exprs in
                if exprs' == exprs then term else Tuple exprs'

            | Focus (focusee, index) ->
                let focusee' = f focusee in
                if focusee' == focusee then term else Focus (focusee', index)

            | TupleT typs ->
                let typs' = Vector.map_children f typs in
                if typs' == typs then term else TupleT typs'

            | Record stmts ->
                let stmts' = Vector.map_children (Stmt.map_child_exprs f) stmts in
                if stmts' == stmts then term else Record stmts'

            | Select (selectee, label) ->
                let selectee' = f selectee in
                if selectee' == selectee then term else Select (selectee', label)

            | RecordT decls ->
                let decls' = Vector.map_children (Decl.map_child_exprs f) decls in
                if decls' == decls then term else RecordT decls'

            | VariantT decls ->
                let decls' = Vector.map_children (Decl.map_child_exprs f) decls in
                if decls' == decls then term else VariantT decls'

            | RowT decls ->
                let decls' = Vector.map_children (Decl.map_child_exprs f) decls in
                if decls' == decls then term else RowT decls'

            | Var _ | Wild _ | Const _ | PrimT _ -> term in

        if term' == term then expr else {expr with v = term}

    let iter_clause_exprs f {params; body} = f params; f body

    let iter_children f (expr : t) =
        match expr.v with
        | Fn clauses | ImpliFn clauses -> Vector.iter (iter_clause_exprs f) clauses

        | App exprs -> Vector.iter f exprs

        | PrimApp (_, exprs) -> Vector.iter f exprs

        | PiT {domain; eff; codomain} ->
            f domain; Option.iter f eff; f codomain

        | ImpliT {domain; codomain} -> f domain; f codomain

        | Ann (expr, typ) -> f expr; f typ

        | Tuple exprs -> Vector.iter f exprs

        | Focus (focusee, _) -> f focusee

        | TupleT typs -> Vector.iter f typs

        | Record stmts -> Vector.iter (Stmt.iter_child_exprs f) stmts

        | Select (selectee, _) -> f selectee

        | RecordT decls -> Vector.iter (Decl.iter_child_exprs f) decls

        | VariantT decls -> Vector.iter (Decl.iter_child_exprs f) decls

        | RowT decls -> Vector.iter (Decl.iter_child_exprs f) decls

        | Var _ | Wild _ | Const _ | PrimT _ -> ()
end

and Stmt : (AstSigs.STMT with type expr = Expr.t) = struct
    type expr = Expr.t

    type def = Util.span * expr * expr

    type t =
        | Def of Util.span * expr * expr
        | Expr of expr

    let pos = function
        | Def (pos, _, _) -> pos
        | Expr expr -> expr.pos

    let to_doc =
        let open PPrint in

        function
        | Def (_, pat, expr) -> infix 4 1 equals (Expr.to_doc pat) (Expr.to_doc expr)
        | Expr expr -> Expr.to_doc expr

    let map_child_exprs f stmt = match stmt with
        | Def (span, pat, expr) ->
            let pat' = f pat in
            let expr' = f expr in
            if pat' == pat && expr' == expr then stmt else Def (span, pat', expr')

        | Expr expr ->
            let expr' = f expr in
            if expr' == expr then stmt else Expr expr'

    let iter_child_exprs f = function
        | Def (_, pat, expr) -> f pat; f expr
        | Expr expr -> f expr
end

and Decl : (AstSigs.DECL with type expr = Expr.t) = struct
    type expr = Expr.t

    type t =
        | Def of Util.span * expr * expr
        | Decl of Util.span * expr * expr
        | Type of expr

    let to_doc =
        let open PPrint in
        function
        | Def (_, pat, expr) -> infix 4 1 equals (Expr.to_doc pat) (Expr.to_doc expr)
        | Decl (_, pat, typ) -> infix 4 1 colon (Expr.to_doc pat) (Expr.to_doc typ)
        | Type typ -> Expr.to_doc typ

    let pos = function
        | Def (pos, _, _) -> pos
        | Decl (pos, _, _) -> pos
        | Type typ -> typ.pos

    let map_child_exprs f stmt = match stmt with
        | Def (span, pat, expr) ->
            let pat' = f pat in
            let expr' = f expr in
            if pat' == pat && expr' == expr then stmt else Def (span, pat', expr')

        | Decl (span, pat, expr) ->
            let pat' = f pat in
            let expr' = f expr in
            if pat' == pat && expr' == expr then stmt else Decl (span, pat', expr')

        | Type expr ->
            let expr' = f expr in
            if expr' == expr then stmt else Type expr'

    let iter_child_exprs f = function
        | Def (_, pat, expr) | Decl (_, pat, expr) -> f pat; f expr
        | Type expr -> f expr
end

module Program = struct
    module Stmt = Stmt
    module Expr = Expr

    type t = {span : span; defs : Stmt.def Vector.t; body : Expr.t}

    let def_to_doc (_, pat, expr) = PPrint.(infix 4 1 equals (Expr.to_doc pat) (Expr.to_doc expr))

    let to_doc {span = _; defs; body} =
        let open PPrint in

        separate_map (semi ^^ twice hardline) def_to_doc (Vector.to_list defs)
        ^^ semi ^^ twice hardline
        ^^ Expr.to_doc body
end

