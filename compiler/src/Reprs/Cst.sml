signature CST = sig
    structure Prim: PRIM_TYPE where type t = PrimType.t

    datatype typ
        = Pi of Pos.t * def * typ
        | RecordT of Pos.t * typ
        | RowExt of Pos.t * {fields: (Name.t * typ) vector, ext: typ}
        | EmptyRow of Pos.t
        | Interface of Pos.t * (Name.t * typ) vector
        | WildRow of Pos.t
        | Singleton of Pos.t * expr
        | TypeT of Pos.t
        | Path of expr
        | Prim of Pos.t * Prim.t

    and expr
        = Fn of Pos.t * Name.t * typ option * expr
        | Let of Pos.t * stmt vector * expr
        | If of Pos.t * expr * expr * expr
        | Record of Pos.t * row
        | Module of Pos.t * stmt vector
        | App of Pos.t * {callee: expr, arg: expr}
        | Field of Pos.t * expr * Name.t
        | Ann of Pos.t * expr * typ
        | Type of Pos.t * typ
        | Use of Pos.t * Name.t
        | Const of Pos.t * Const.t

    and stmt
        = Val of Pos.t * Name.t * typ option * expr
        | Expr of expr

    withtype def = {var: Name.t, typ: typ option}
    and row = {fields: (Name.t * expr) vector, ext: expr option}

    structure Type: sig
        structure Prim: PRIM_TYPE where type t = PrimType.t

        datatype typ = datatype typ

        val pos: typ -> Pos.t
        val toDoc: typ -> PPrint.t
        val toString: typ -> string
    end

    structure Term: sig
        datatype expr = datatype expr
        datatype stmt = datatype stmt
        type def = def
        type row = row

        val exprPos: expr -> Pos.t
        val exprToDoc: expr -> PPrint.t
        val exprToString: expr -> string
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

    datatype typ
        = Pi of Pos.t * def * typ
        | RecordT of Pos.t * typ
        | RowExt of Pos.t * {fields: (Name.t * typ) vector, ext: typ}
        | EmptyRow of Pos.t
        | Interface of Pos.t * (Name.t * typ) vector
        | WildRow of Pos.t
        | Singleton of Pos.t * expr
        | TypeT of Pos.t
        | Path of expr
        | Prim of Pos.t * Prim.t

    and expr
        = Fn of Pos.t * Name.t * typ option * expr
        | Let of Pos.t * stmt vector * expr
        | If of Pos.t * expr * expr * expr
        | Record of Pos.t * row
        | Module of Pos.t * stmt vector
        | App of Pos.t * {callee: expr, arg: expr}
        | Field of Pos.t * expr * Name.t
        | Ann of Pos.t * expr * typ
        | Type of Pos.t * typ
        | Use of Pos.t * Name.t
        | Const of Pos.t * Const.t

    and stmt
        = Val of Pos.t * Name.t * typ option * expr
        | Expr of expr

    withtype def = {var: Name.t, typ: typ option}
    and row = {fields: (Name.t * expr) vector, ext: expr option}

    val exprPos =
        fn Fn (pos, _, _, _) => pos
         | Let (pos, _, _) => pos
         | If (pos, _, _, _) => pos
         | Record (pos, _) => pos
         | Module (pos, _) => pos
         | App (pos, _) => pos
         | Field (pos, _, _) => pos
         | Ann (pos, _, _) => pos
         | Type (pos, _) => pos
         | Use (pos, _) => pos
         | Const (pos, _) => pos

    val typePos =
        fn Pi (pos, _, _) => pos
         | RecordT (pos, _) => pos
         | RowExt (pos, _) => pos
         | EmptyRow pos => pos
         | WildRow pos => pos
         | Singleton (pos, _) => pos
         | TypeT pos => pos
         | Path expr => exprPos expr
         | Prim (pos, _) => pos

    val rec typeToDoc =
        fn Pi (_, {var, typ = domain}, codomain) =>
            text "fun" <+> Name.toDoc var <> annToDoc domain
                <+> text "->" <+> typeToDoc codomain
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
            let fun declToDoc (label, t) = Name.toDoc label <+> text ":" <+> typeToDoc t
            in text "interface"
                   <> (PPrint.nest 4 (PPrint.punctuate newline
                                                       (Vector.map declToDoc decls)))
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
        fn Fn (_, param, ann, body) =>
               text "fn" <+> Name.toDoc param <> annToDoc ann <> text " => " <> exprToDoc body
         | If (_, cond, conseq, alt) =>
            text "if" <+> exprToDoc cond
                <+> text "then" <+> exprToDoc conseq
                <+> text "else" <+> exprToDoc alt
         | Record (_, row) => braces (rowToDoc row)
         | Module (_, stmts) =>
            text "module"
                <> (PPrint.nest 4 (newline <> PPrint.punctuate newline (Vector.map stmtToDoc stmts)))
                <++> text "end"
         | App (_, {callee, arg}) => parens (exprToDoc callee <+> exprToDoc arg)
         | Field (_, expr, label) => parens (exprToDoc expr <> text "." <> Name.toDoc label)
         | Let (_, stmts, body) =>
            text "let" <+> PPrint.align (PPrint.punctuate newline (Vector.map stmtToDoc stmts))
                <++> text "in" <+> exprToDoc body
                <++> text "end"
         | Ann (_, expr, t) => exprToDoc expr <> text ":" <+> typeToDoc t
         | Type (_, t) => text "type" <+> typeToDoc t
         | Use (_, name) => Name.toDoc name
         | Const (_, c) => Const.toDoc c
    
    and rowToDoc = 
        fn {fields, ext} =>
            let fun entryToDoc (label, expr) = Name.toDoc label <+> text "=" <+> exprToDoc expr
                val fieldsDoc = PPrint.punctuate (text ", ") (Vector.map entryToDoc fields)
                val extDoc = Option.mapOr (fn ext => text " .." <+> exprToDoc ext) PPrint.empty ext
            in fieldsDoc <> extDoc
            end

    and stmtToDoc =
        fn Val (_, name, ann, valExpr) =>
            text "val " <> Name.toDoc name <> annToDoc ann <> text " = " <> exprToDoc valExpr
         | Expr expr => exprToDoc expr

    structure Type = struct
        structure Prim = PrimType

        datatype typ = datatype typ
        type def = def

        val pos = typePos
        val toDoc = typeToDoc
        val toString = PPrint.pretty 80 o toDoc
    end

    structure Term = struct
        datatype expr = datatype expr
        datatype stmt = datatype stmt
        type def = def
        type row = row

        val exprPos = exprPos
        val exprToDoc = exprToDoc
        val exprToString = PPrint.pretty 80 o exprToDoc
    end
end

