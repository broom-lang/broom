signature CST = sig
    structure Prim: PRIM_TYPE where type t = PrimType.t

    datatype 'eff explicitness = Implicit | Explicit of 'eff

    datatype effect = Pure | Impure

    type expl = unit explicitness
    type arrow = effect explicitness

    datatype typ
        = Pi of Pos.span * def * arrow * typ
        | RecordT of Pos.span * typ
        | RowExt of Pos.span * row
        | EmptyRow of Pos.span
        | Interface of Pos.span * {var: Name.t option, typ : typ} option
                     * (Pos.span * Name.t * typ) vector
        | WildRow of Pos.span
        | Singleton of Pos.span * expr
        | TypeT of Pos.span
        | Path of expr
        | Prim of Pos.span * Prim.t

    and row_edit
        = WithT of (Name.t * typ) vector
        | WhereT of (Name.t * typ) vector

    and expr
        = Fn of Pos.span * expl * clause vector
        | Begin of Pos.span * stmt vector * expr
        | Do of Pos.span * stmt vector * expr
        | Match of Pos.span * expr * clause vector
        | Record of Pos.span * recordFields
        | Module of Pos.span * (pat option * expr) option * stmt vector
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

    and rec_edit
        = With of (Name.t * expr) vector
        | Where of (Name.t * expr) vector

    withtype def = {var: Name.t, typ: typ option}
    and clause = {pattern: pat, body: expr}
    and recordFields =
        { base : expr option
        , edits : rec_edit vector }
    and row =
        { base : typ
        , edits : row_edit vector }

    val explDoc: expl -> PPrint.t
    val arrowDoc: arrow -> PPrint.t

    structure Type: sig
        structure Prim: PRIM_TYPE where type t = PrimType.t

        datatype typ = datatype typ
        datatype row_edit = datatype row_edit

        val pos: typ -> Pos.span
    end

    structure Term: sig
        datatype expr = datatype expr
        datatype stmt = datatype stmt
        datatype pat = datatype pat
        datatype rec_edit = datatype rec_edit
        type recordFields = recordFields

        val emptyRecord : Pos.span -> expr
        val exprPos: expr -> Pos.span
        val exprToDoc: expr -> PPrint.t
        val exprToString: expr -> string
        val stmtsToDoc: stmt vector -> PPrint.t
    end
end

structure Cst :> CST = struct
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>
    val text = PPrint.text
    val space = PPrint.space
    val newline = PPrint.newline
    val comma = PPrint.comma
    val parens = PPrint.parens
    val braces = PPrint.braces
    val punctuate = PPrint.punctuate

    structure Prim = PrimType

    datatype 'eff explicitness = Implicit | Explicit of 'eff

    datatype effect = Pure | Impure

    type arrow = effect explicitness
    type expl = unit explicitness

    datatype typ
        = Pi of Pos.span * def * arrow * typ
        | RecordT of Pos.span * typ
        | RowExt of Pos.span * row
        | EmptyRow of Pos.span
        | Interface of Pos.span * {var: Name.t option, typ : typ} option
                     * (Pos.span * Name.t * typ) vector
        | WildRow of Pos.span
        | Singleton of Pos.span * expr
        | TypeT of Pos.span
        | Path of expr
        | Prim of Pos.span * Prim.t

    and row_edit
        = WithT of (Name.t * typ) vector
        | WhereT of (Name.t * typ) vector

    and expr
        = Fn of Pos.span * expl * clause vector
        | Begin of Pos.span * stmt vector * expr
        | Do of Pos.span * stmt vector * expr
        | Match of Pos.span * expr * clause vector
        | Record of Pos.span * recordFields
        | Module of Pos.span * (pat option * expr) option * stmt vector
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

    and rec_edit
        = With of (Name.t * expr) vector
        | Where of (Name.t * expr) vector

    withtype def = {var: Name.t, typ: typ option}
    and clause = {pattern: pat, body: expr}
    and recordFields =
        { base : expr option
        , edits : rec_edit vector }
    and row =
        { base : typ
        , edits : row_edit vector }

    val exprPos =
        fn Fn (pos, _, _) => pos
         | Begin (pos, _, _) => pos
         | Do (pos, _, _) => pos
         | Match (pos, _, _) => pos
         | Record (pos, _) => pos
         | Module (pos, _, _) => pos
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
         | Interface (pos, _, _) => pos
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
        fn Pi (_, param, arrow, codomain) =>
            text "fun" <+> defToDoc param <+> arrowDoc arrow <+> typeToDoc codomain
         | RecordT (_, row) => braces (typeToDoc row)
         | RowExt (_, {base, edits}) =>
            let fun fieldToDoc (label, fieldt) = 
                    Name.toDoc label <> text ": " <> typeToDoc fieldt
                fun fieldsToDoc fields =
                    PPrint.punctuate (text ", ") (Vector.map fieldToDoc fields)
                val editToDoc =
                    fn WithT fields => text "where" <+> fieldsToDoc fields
                     | WhereT fields => text "where" <+> fieldsToDoc fields
                val editsDoc =
                    PPrint.punctuate (text " ") (Vector.map editToDoc edits)
            in typeToDoc base <+> editsDoc
            end
         | EmptyRow _ => text "(||)"
         | Interface (_, super, decls) =>
            let fun declToDoc (_, label, t) = text "val" <+> Name.toDoc label <+> text ":" <+> typeToDoc t
            in text "interface"
                   <> (case super
                       of SOME {var = SOME var, typ} => text "extends" <+> defToDoc {var, typ = SOME typ}
                        | SOME {var = NONE, typ} => text "extends" <+> typeToDoc typ
                        | NONE => PPrint.empty)
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
         | Module (pos, super, stmts) =>
            text "module"
                <> (case super
                    of SOME (SOME pat, expr) => text "extends" <+> stmtToDoc (Val (pos, pat, expr))
                     | SOME (NONE, expr) => text "extends" <+> exprToDoc expr
                     | NONE => PPrint.empty)
                <> (PPrint.nest 4 (newline <> stmtsToDoc stmts))
                <++> text "end"
         | App (_, {callee, arg}) => parens (exprToDoc callee <+> exprToDoc arg)
         | Field (_, expr, label) => parens (exprToDoc expr <> text "." <> Name.toDoc label)
         | Begin (_, stmts, body) =>
            text "begin" <+> PPrint.align (stmtsToDoc stmts)
                <++> PPrint.semi <+> exprToDoc body
                <++> text "end"
         | Do (_, stmts, body) =>
            text "do" <+> PPrint.align (stmtsToDoc stmts)
                <++> PPrint.semi <+> exprToDoc body
                <++> text "end"
         | Ann (_, expr, t) => exprToDoc expr <> text ":" <+> typeToDoc t
         | Type (_, t) => text "type" <+> typeToDoc t
         | Use (_, name) => Name.toDoc name
         | Const (_, c) => Const.toDoc c

    and defToDoc = fn {var, typ} => Name.toDoc var <> annToDoc typ

    and fieldToDoc =
        fn (name, expr) => Name.toDoc name <+> text "=" <+> exprToDoc expr

    and fieldsToDoc =
        fn fields => PPrint.punctuate (space <> comma) (Vector.map fieldToDoc fields)

    and editToDoc =
        fn With fields => text "with" <+> fieldsToDoc fields
         | Where fields => text "where" <+> fieldsToDoc fields

    and editsToDoc =
        fn edits => punctuate space (Vector.map editToDoc edits)
    
    and rowToDoc = 
        fn {base = SOME base, edits} => exprToDoc base <+> editsToDoc edits
         | {base = NONE, edits} =>
            (case Vector.uncons edits
             of SOME (With startFields, edits) =>
                 fieldsToDoc startFields <+> editsToDoc (VectorSlice.vector edits)
              | SOME (Where _, _) => editsToDoc edits
              | NONE => PPrint.empty)

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
        datatype row_edit = datatype row_edit

        val pos = typePos
    end

    structure Term = struct
        datatype expr = datatype expr
        datatype stmt = datatype stmt
        datatype pat = datatype pat
        datatype rec_edit = datatype rec_edit
        type recordFields = recordFields

        fun emptyRecord pos = Record (pos, {base = NONE, edits = #[]})
        val exprPos = exprPos
        val exprToDoc = exprToDoc
        val exprToString = PPrint.pretty 80 o exprToDoc
        val stmtsToDoc = stmtsToDoc
    end
end

