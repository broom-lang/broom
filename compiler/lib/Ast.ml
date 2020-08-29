let (^^) = PPrint.(^^)
let (^/^) = PPrint.(^/^)

(* FIXME: Printing syntax differs from parsed syntax: *)

type 'a with_pos = 'a Util.with_pos

module rec Term : AstSigs.TERM with type Expr.typ = Type.t = struct
    module Expr = struct
        module Stmt = Term.Stmt

        type typ = Type.t
        type stmt = Stmt.t

        type t =
            | Values of t with_pos Vector.t
            | Ann of t with_pos * typ with_pos
            | Fn of clause Vector.t
            | Thunk of stmt Vector.t
            | App of t with_pos * t with_pos Vector.t
            | AppSequence of t with_pos Vector1.t
            | PrimApp of Primop.t * t with_pos Vector.t
            | Record of stmt Vector.t
            | Select of t with_pos * Name.t
            | Proxy of typ
            | Var of Name.t
            | Const of Const.t

        and clause =
            { iparams : pat with_pos Vector.t
            ; eparams : pat with_pos Vector.t
            ; body : t with_pos }

        and pat = t

        let rec to_doc (expr : t with_pos) = match expr.v with
            | Values val_exprs ->
                PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.empty)
                    PPrint.lparen (PPrint.comma ^^ PPrint.break 1) PPrint.rparen
                    to_doc (Vector.to_list val_exprs)
            | Fn clauses ->
                PPrint.separate_map (PPrint.break 1) clause_to_doc (Vector.to_list clauses)
                |> PPrint.brackets
            | Thunk stmts ->
                PPrint.surround_separate_map 4 0 (PPrint.brackets PPrint.empty)
                    PPrint.lbracket (PPrint.semi ^^ PPrint.break 1) PPrint.rbracket
                    Stmt.to_doc (Vector.to_list stmts)
            | App (callee, args) -> to_doc callee
                ^/^ PPrint.separate_map (PPrint.break 1) to_doc (Vector.to_list args)
            | AppSequence exprs ->
                PPrint.separate_map (PPrint.break 1) to_doc (Vector1.to_list exprs)
            | PrimApp (callee, args) -> PPrint.string "__" ^^ Primop.to_doc callee
                ^/^ PPrint.separate_map (PPrint.break 1) to_doc (Vector.to_list args)
            | Ann (expr, typ) ->
                PPrint.infix 4 1 PPrint.colon (to_doc expr) (Type.to_doc typ)
            | Record stmts ->
                PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.empty)
                    PPrint.lbrace (PPrint.semi ^^ PPrint.break 1) PPrint.rbrace
                    Stmt.to_doc (Vector.to_list stmts)
            | Select (record, label) -> to_doc record ^^ PPrint.dot ^^ Name.to_doc label
            | Proxy typ -> Type.to_doc {expr with v = typ}
            | Var name -> Name.to_doc name
            | Const v -> Const.to_doc v

        and clause_to_doc {iparams; eparams; body} =
            let idoc = PPrint.separate_map (PPrint.break 1) to_doc (Vector.to_list iparams) in
            let edoc = PPrint.separate_map (PPrint.break 1) to_doc (Vector.to_list eparams) in
            PPrint.bar ^^ PPrint.blank 1
                ^^ PPrint.infix 4 1 (PPrint.string "->")
                    (PPrint.infix 4 1 (PPrint.string "=>") idoc edoc)
                    (to_doc body)
    end

    module Stmt = struct
        type expr = Expr.t
        type pat = Expr.pat

        type def = Util.span * pat with_pos * expr with_pos

        type t =
            | Def of def
            | Expr of expr with_pos

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
        | Pi of pat with_pos * t with_pos * t with_pos
        | Record of stmt Vector.t
        | Row of stmt Vector.t
        | Path of expr
        | Prim of Prim.t

    and 'a decl = {name : 'a; typ : t with_pos}

    let rec to_doc (typ : t with_pos) = match typ.v with
        | Pi (domain, eff, codomain) ->
            PPrint.infix 4 1 (PPrint.string "-!") (Term.Expr.to_doc domain)
                (PPrint.infix 4 1 (PPrint.string "->") (to_doc eff) (to_doc codomain))
        | Record stmts ->
            PPrint.surround_separate_map 4 0 (PPrint.braces PPrint.bar)
                (PPrint.lbrace ^^ PPrint.bar) (PPrint.semi ^^ PPrint.break 1) (PPrint.bar ^^ PPrint.rbrace)
                Term.Stmt.to_doc (Vector.to_list stmts)
        | Row stmts ->
            PPrint.surround_separate_map 4 0 (PPrint.parens PPrint.bar)
                (PPrint.lparen ^^ PPrint.bar) (PPrint.semi ^^ PPrint.break 1) (PPrint.bar ^^ PPrint.rparen)
                Term.Stmt.to_doc (Vector.to_list stmts)
        | Path expr -> Term.Expr.to_doc {typ with v = expr}
        | Prim pt -> Prim.to_doc pt
end

