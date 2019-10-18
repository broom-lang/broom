signature CST = sig
    structure Prim: PRIM_TYPE where type t = PrimType.t

    datatype 'eff explicitness = Implicit | Explicit of 'eff

    datatype effect = Pure | Impure

    type expl = unit explicitness
    type arrow = effect explicitness

    datatype typ
        = Pi of Pos.span * def * arrow * typ
        | RecordT of Pos.span * typ
        | RowExt of Pos.span * {fields: (Name.t * typ) vector, ext: typ}
        | EmptyRow of Pos.span
        | Interface of Pos.span * (Pos.span * Name.t * typ) vector
        | WildRow of Pos.span
        | Singleton of Pos.span * expr
        | TypeT of Pos.span
        | Path of expr
        | Prim of Pos.span * Prim.t

    and expr
        = Fn of Pos.span * expl * clause vector
        | Let of Pos.span * stmt vector * expr
        | Match of Pos.span * expr * clause vector
        | Record of Pos.span * row
        | Module of Pos.span * stmt vector
        | App of Pos.span * {callee: expr, arg: expr}
        | Field of Pos.span * expr * Name.t
        | Ann of Pos.span * expr * typ
        | Type of Pos.span * typ
        | Use of Pos.span * Name.t
        | Const of Pos.span * Const.t

    and stmt
        = Val of Pos.span * pat * expr
        | Expr of expr

    and pat
        = AnnP of Pos.span * {pat: pat, typ: typ}
        | Def of Pos.span * Name.t
        | ConstP of Pos.span * Const.t

    withtype def = {var: Name.t, typ: typ option}
    and clause = {pattern: pat, body: expr}
    and row = {fields: (Name.t * expr) vector, ext: expr option}

    val explDoc: expl -> PPrint.t
    val arrowDoc: arrow -> PPrint.t

    structure Type: sig
        structure Prim: PRIM_TYPE where type t = PrimType.t

        datatype typ = datatype typ

        val pos: typ -> Pos.span
        val toDoc: typ -> PPrint.t
    end

    structure Term: sig
        datatype expr = datatype expr
        datatype stmt = datatype stmt
        datatype pat = datatype pat
        type def = def
        type row = row

        val exprPos: expr -> Pos.span
        val exprToDoc: expr -> PPrint.t
        val exprToString: expr -> string
        val stmtToDoc: stmt -> PPrint.t
        val stmtsToDoc: stmt vector -> PPrint.t
    end
end

structure Cst :> CST = struct
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>
    val text = PPrint.text
    val newline = PPrint.newline
    val parens = PPrint.parens
    val braces = PPrint.braces

    structure Prim = PrimType

    datatype 'eff explicitness = Implicit | Explicit of 'eff

    datatype effect = Pure | Impure

    type arrow = effect explicitness
    type expl = unit explicitness

    datatype typ
        = Pi of Pos.span * def * arrow * typ
        | RecordT of Pos.span * typ
        | RowExt of Pos.span * {fields: (Name.t * typ) vector, ext: typ}
        | EmptyRow of Pos.span
        | Interface of Pos.span * (Pos.span * Name.t * typ) vector
        | WildRow of Pos.span
        | Singleton of Pos.span * expr
        | TypeT of Pos.span
        | Path of expr
        | Prim of Pos.span * Prim.t

    and expr
        = Fn of Pos.span * expl * clause vector
        | Let of Pos.span * stmt vector * expr
        | Match of Pos.span * expr * clause vector
        | Record of Pos.span * row
        | Module of Pos.span * stmt vector
        | App of Pos.span * {callee: expr, arg: expr}
        | Field of Pos.span * expr * Name.t
        | Ann of Pos.span * expr * typ
        | Type of Pos.span * typ
        | Use of Pos.span * Name.t
        | Const of Pos.span * Const.t

    and stmt
        = Val of Pos.span * pat * expr
        | Expr of expr

    and pat
        = AnnP of Pos.span * {pat: pat, typ: typ}
        | Def of Pos.span * Name.t
        | ConstP of Pos.span * Const.t

    withtype def = {var: Name.t, typ: typ option}
    and clause = {pattern: pat, body: expr}
    and row = {fields: (Name.t * expr) vector, ext: expr option}

    val exprPos =
        fn Fn (pos, _, _) => pos
         | Let (pos, _, _) => pos
         | Match (pos, _, _) => pos
         | Record (pos, _) => pos
         | Module (pos, _) => pos
         | App (pos, _) => pos
         | Field (pos, _, _) => pos
         | Ann (pos, _, _) => pos
         | Type (pos, _) => pos
         | Use (pos, _) => pos
         | Const (pos, _) => pos

    val typePos =
        fn Pi (pos, _, _, _) => pos
         | RecordT (pos, _) => pos
         | RowExt (pos, _) => pos
         | EmptyRow pos => pos
         | WildRow pos => pos
         | Interface (pos, _) => pos
         | Singleton (pos, _) => pos
         | TypeT pos => pos
         | Path expr => exprPos expr
         | Prim (pos, _) => pos

    val arrowDoc =
        fn Implicit => text "=>"
         | Explicit Pure => text "->"
         | Explicit Impure => text "~>"

    val explDoc =
        fn Implicit => arrowDoc Implicit
         | Explicit () => arrowDoc (Explicit Pure)

    val rec typeToDoc =
        fn Pi (_, {var, typ = domain}, arrow, codomain) =>
            text "fun" <+> Name.toDoc var <> annToDoc domain
                <+> arrowDoc arrow <+> typeToDoc codomain
         | RecordT (_, row) => braces (typeToDoc row)
         | RowExt (_, {fields, ext}) =>
            let fun fieldToDoc (label, fieldt) = 
                    Name.toDoc label <> text ": " <> typeToDoc fieldt
                val fieldsDoc =
                    PPrint.punctuate (text ", ") (Vector.map fieldToDoc fields)
            in fieldsDoc <+> text "|" <+> typeToDoc ext
            end
         | EmptyRow _ => text "(||)"
         | Interface (_, decls) =>
            let fun declToDoc (_, label, t) = text "val" <+> Name.toDoc label <+> text ":" <+> typeToDoc t
            in text "interface"
                   <> (PPrint.nest 4 (newline <> PPrint.punctuate newline (Vector.map declToDoc decls)))
                   <++> text "end"
            end
         | WildRow _ => text ".."
         | Singleton (_, expr) => parens (text "= " <> exprToDoc expr)
         | TypeT _ => text "type"
         | Path expr => exprToDoc expr
         | Prim (_, p) => Prim.toDoc p

    and annToDoc =
        fn SOME t => text ":" <+> typeToDoc t
         | NONE => PPrint.empty

    and exprToDoc =
        fn Fn (_, arrow, clauses) =>
            braces (PPrint.align (clausesToDoc arrow clauses))
         | Match (_, matchee, clauses) =>
            text "match" <+> exprToDoc matchee
                <+> braces (PPrint.align (clausesToDoc (Explicit ()) clauses))
         | Record (_, row) => braces (rowToDoc row)
         | Module (_, stmts) =>
            text "module"
                <> (PPrint.nest 4 (newline <> stmtsToDoc stmts))
                <++> text "end"
         | App (_, {callee, arg}) => parens (exprToDoc callee <+> exprToDoc arg)
         | Field (_, expr, label) => parens (exprToDoc expr <> text "." <> Name.toDoc label)
         | Let (_, stmts, body) =>
            text "let" <+> PPrint.align (stmtsToDoc stmts)
                <++> text "in" <+> exprToDoc body
                <++> text "end"
         | Ann (_, expr, t) => exprToDoc expr <> text ":" <+> typeToDoc t
         | Type (_, t) => text "type" <+> typeToDoc t
         | Use (_, name) => Name.toDoc name
         | Const (_, c) => Const.toDoc c

    and defToDoc = fn {var, typ} => Name.toDoc var <> annToDoc typ
    
    and rowToDoc = 
        fn {fields, ext} =>
            let fun entryToDoc (label, expr) = Name.toDoc label <+> text "=" <+> exprToDoc expr
                val fieldsDoc = PPrint.punctuate (text ", ") (Vector.map entryToDoc fields)
                val extDoc = Option.mapOr (fn ext => text " .." <+> exprToDoc ext) PPrint.empty ext
            in fieldsDoc <> extDoc
            end

    and clauseToDoc = fn expl => fn {pattern, body} =>
        patToDoc pattern <+> explDoc expl <+> exprToDoc body
    and clausesToDoc = fn expl => fn clauses =>
        PPrint.punctuate newline (Vector.map (clauseToDoc expl) clauses)

    and stmtToDoc =
        fn Val (_, pat, valExpr) =>
            text "val" <+> patToDoc pat <+> text " = " <> exprToDoc valExpr
         | Expr expr => exprToDoc expr

    and stmtsToDoc =
        fn stmts => PPrint.punctuate newline (Vector.map stmtToDoc stmts)

    and patToDoc =
        fn AnnP (_, {pat, typ}) => patToDoc pat <> text ":" <+> typeToDoc typ
         | Def (_, name) => Name.toDoc name
         | ConstP (_, c) => Const.toDoc c

    structure Type = struct
        structure Prim = PrimType

        datatype typ = datatype typ

        val pos = typePos
        val toDoc = typeToDoc
    end

    structure Term = struct
        datatype expr = datatype expr
        datatype stmt = datatype stmt
        datatype pat = datatype pat
        type def = def
        type row = row

        val exprPos = exprPos
        val exprToDoc = exprToDoc
        val exprToString = PPrint.pretty 80 o exprToDoc
        val stmtToDoc = stmtToDoc
        val stmtsToDoc = stmtsToDoc
    end
end

