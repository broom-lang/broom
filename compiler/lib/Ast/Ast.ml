let (^^) = PPrint.(^^)

(* FIXME: Printing syntax differs from parsed syntax: *)

type 'a with_pos = 'a Util.with_pos

module rec Term : AstSigs.TERM with type Expr.typ = Type.t = struct
    module Expr = struct
        module Stmt = Term.Stmt

        type typ = Type.t
        type stmt = Stmt.t

        type t =
            | Values of t with_pos Vector.t
            | Focus of t with_pos * int
            | Ann of t with_pos * typ with_pos
            | Fn of clause Vector.t
            | App of t with_pos * (t with_pos, t with_pos) Ior.t
            | AppSequence of t with_pos Vector1.t
            | PrimApp of Primop.t * (t with_pos, t with_pos) Ior.t
            | Record of stmt Vector.t
            | Select of t with_pos * Name.t
            | Proxy of typ
            | Var of Name.t
            | Wild
            | Const of Const.t

        and clause = {params : (pat with_pos, pat with_pos) Ior.t; body : t with_pos}

        and pat = t

        let rec to_doc (expr : t with_pos) = match expr.v with
            | Values val_exprs ->
                PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                    PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                    to_doc (Vector.to_list val_exprs)
            | Focus (tup, i) -> to_doc tup ^^ PPrint.dot ^^ PPrint.string (Int.to_string i)
            | Fn clauses ->
                PPrint.separate_map (PPrint.break 1) clause_to_doc (Vector.to_list clauses)
                |> PPrint.braces
            | App (callee, args) -> PPrint.prefix 4 1 (to_doc callee) (args_to_doc args)
            | AppSequence exprs ->
                PPrint.separate_map (PPrint.break 1) to_doc (Vector1.to_list exprs)
            | PrimApp (callee, args) ->
                PPrint.prefix 4 1 (PPrint.string "__" ^^ Primop.to_doc callee)
                    (args_to_doc args)
            | Ann (expr, typ) ->
                PPrint.infix 4 1 PPrint.colon (to_doc expr) (Type.to_doc typ)
            | Record stmts ->
                PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                    PPrint.lbrace (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
                    Stmt.to_doc (Vector.to_list stmts)
            | Select (record, label) -> to_doc record ^^ PPrint.dot ^^ Name.to_doc label
            | Proxy typ -> Type.to_doc {expr with v = typ}
            | Var name -> Name.to_doc name
            | Wild -> PPrint.underscore
            | Const v -> Const.to_doc v

        and clause_to_doc {params; body} = match params with
            | Left iparam ->
                PPrint.infix 4 1 PPrint.qmark (PPrint.qmark ^^ PPrint.blank 1 ^^ to_doc iparam)
                    (to_doc body)
            | Right eparam ->
                PPrint.infix 4 1 PPrint.bar (PPrint.bar ^^ PPrint.blank 1 ^^ to_doc eparam)
                    (to_doc body)
            | Both (iparam, eparam) ->
                PPrint.infix 4 1 PPrint.bar (to_doc eparam) (to_doc body)
                |> PPrint.infix 4 1 PPrint.bar (PPrint.qmark ^^ PPrint.blank 1 ^^ to_doc iparam)

        and args_to_doc = function
            | Left iarg -> to_doc iarg ^^ PPrint.blank 1 ^^ PPrint.string "@"
            | Right earg -> to_doc earg
            | Both (iarg, earg) ->
                PPrint.infix 4 1 (PPrint.string "@") (to_doc iarg) (to_doc earg)
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
            PPrint.infix 4 1 PPrint.equals (Expr.to_doc pat) (Expr.to_doc expr)

        let to_doc = function
            | Def def -> def_to_doc def
            | Expr expr -> Expr.to_doc expr
    end
end

and Type : AstSigs.TYPE
    with type expr = Term.Expr.t
    with type pat = Term.Expr.pat
    with type stmt = Term.Stmt.t
= struct
    type expr = Term.Expr.t
    type pat = Term.Expr.pat
    type stmt = Term.Stmt.t

    type t =
        | Values of t with_pos Vector.t
        | Pi of {domain : (pat with_pos, (pat with_pos * t with_pos option)) Ior.t; codomain : t with_pos }
        | Record of stmt Vector.t
        | Row of stmt Vector.t
        | Path of expr
        | Prim of Prim.t

    let rec to_doc (typ : t with_pos) = match typ.v with
        | Values typs ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.colon)
                (PPrint.lparen ^^ PPrint.colon) (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                to_doc (Vector.to_list typs)
        | Pi {domain; codomain} ->
            let codoc = to_doc codomain in
            let (idoc, edoc, effdoc) = match domain with
                | Left idomain -> (Some (Term.Expr.to_doc idomain), None, None)
                | Right (edomain, eff) -> (None, Some (Term.Expr.to_doc edomain), Option.map to_doc eff)
                | Both (idomain, (edomain, eff)) ->
                    ( Some (Term.Expr.to_doc idomain), Some (Term.Expr.to_doc edomain)
                    , Option.map to_doc eff ) in
            let doc = match edoc with
                | Some edoc ->
                    let doc = PPrint.string "->" ^^ PPrint.blank 1 ^^ codoc in
                    let doc = match effdoc with
                        | Some effdoc ->
                            PPrint.prefix 4 1 (PPrint.string "-!" ^^ PPrint.blank 1 ^^ effdoc) doc
                        | None -> doc in
                    PPrint.prefix 4 1 edoc doc
                | None -> codoc in
            (match idoc with
            | Some idoc -> PPrint.prefix 4 1 idoc (PPrint.string "=>" ^^ PPrint.blank 1 ^^ doc)
            | None -> doc)
        | Record stmts ->
            PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.colon)
                (PPrint.lbrace ^^ PPrint.colon) (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
                Term.Stmt.to_doc (Vector.to_list stmts)
        | Row stmts ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.bar)
                (PPrint.lparen ^^ PPrint.bar) (PPrint.break 1 ^^ PPrint.bar ^^ PPrint.break 1) PPrint.rparen
                Term.Stmt.to_doc (Vector.to_list stmts)
        | Path expr -> Term.Expr.to_doc {typ with v = expr}
        | Prim pt -> Prim.to_doc pt
end

