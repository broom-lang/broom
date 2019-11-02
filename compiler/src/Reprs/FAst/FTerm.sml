signature FAST_TERM = sig
    structure Type: CLOSED_FAST_TYPE

    type arrow = Type.arrow

    type def = {pos: Pos.span, id: DefId.t, var: Name.t, typ: Type.concr}

    datatype expr
        = Fn of Pos.span * def * arrow * expr
        | TFn of Pos.span * Type.def vector * expr
        | EmptyRecord of Pos.span
        | With of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
        | Without of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
        | Where of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
        | App of Pos.span * Type.concr * {callee: expr, arg: expr}
        | TApp of Pos.span * Type.concr * {callee: expr, args: Type.concr vector}
        | Field of Pos.span * Type.concr * expr * Name.t
        | Let of Pos.span * stmt vector * expr
        | Match of Pos.span * Type.concr * expr * clause vector
        | Cast of Pos.span * Type.concr * expr * Type.co
        | Type of Pos.span * Type.abs
        | Use of Pos.span * def
        | Const of Pos.span * Const.t

    and stmt
        = Val of Pos.span * def * expr
        | Axiom of Pos.span * Name.t * Type.concr * Type.concr
        | Expr of expr

    and pat
        = Def of Pos.span * def
        | ConstP of Pos.span * Const.t

    withtype clause = {pattern: pat, body: expr}

    type program = { typeFns: (Name.t * Type.tfn_sig) vector
                   , axioms: (Name.t * Type.concr * Type.concr) vector
                   , scope: ScopeId.t
                   , stmts: stmt vector
                   , sourcemap: Pos.sourcemap }
   
    val updateDefTyp : {pos: Pos.span, id: DefId.t, var: Name.t, typ: 't} -> ('t -> 'u)
                     -> {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'u}
    val setDefTyp : {pos: Pos.span, id: DefId.t, var: Name.t, typ: 't} -> 'u
                  -> {pos: Pos.span, id: DefId.t, var: Name.t, typ: 'u}
    val defToDoc : def -> PPrint.t
    val exprPos: expr -> Pos.span
    val exprToDoc: expr -> PPrint.t
    val exprToString: expr -> string
    val stmtPos: stmt -> Pos.span
    val stmtToDoc: stmt -> PPrint.t
    val stmtsToDoc: stmt vector -> PPrint.t
    val patPos: pat -> Pos.span
    val patternToDoc: pat -> PPrint.t
    val programToDoc: program -> PPrint.t
    val typeOf: expr -> Type.concr
end

functor FTerm (Type: CLOSED_FAST_TYPE) :> FAST_TERM
    where type Type.sv = Type.sv
= struct
    val op|> = Fn.|>
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>
    val op<|> = PPrint.<|>
    val space = PPrint.space
    val newline = PPrint.newline
    val parens = PPrint.parens
    val brackets = PPrint.brackets
    val braces = PPrint.braces
    val punctuate = PPrint.punctuate
    val align = PPrint.align

    structure Type = Type

    type arrow = Type.arrow

    type def = {pos: Pos.span, id: DefId.t, var: Name.t, typ: Type.concr}

    datatype expr
        = Fn of Pos.span * def * arrow * expr
        | TFn of Pos.span * Type.def vector * expr
        | EmptyRecord of Pos.span
        | With of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
        | Without of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
        | Where of Pos.span * Type.concr * {base : expr, field : Name.t * expr}
        | App of Pos.span * Type.concr * {callee: expr, arg: expr}
        | TApp of Pos.span * Type.concr * {callee: expr, args: Type.concr vector}
        | Field of Pos.span * Type.concr * expr * Name.t
        | Let of Pos.span * stmt vector * expr
        | Match of Pos.span * Type.concr * expr * clause vector
        | Cast of Pos.span * Type.concr * expr * Type.co
        | Type of Pos.span * Type.abs
        | Use of Pos.span * def
        | Const of Pos.span * Const.t

    and stmt
        = Val of Pos.span * def * expr
        | Axiom of Pos.span * Name.t * Type.concr * Type.concr
        | Expr of expr

    and pat
        = Def of Pos.span * def
        | ConstP of Pos.span * Const.t

    withtype clause = {pattern: pat, body: expr}

    val exprPos =
        fn Fn (pos, _, _, _) => pos
         | TFn (pos, _, _) => pos
         | App (pos, _, _) => pos
         | TApp (pos, _, _) => pos
         | Field (pos, _, _, _) => pos
         | Let (pos, _, _) => pos
         | Match (pos, _, _, _) => pos
         | Cast (pos, _, _, _) => pos
         | Type (pos, _) => pos
         | Use (pos, _) => pos
         | Const (pos, _) => pos

    type program = { typeFns: (Name.t * Type.tfn_sig) vector
                   , axioms: (Name.t * Type.concr * Type.concr) vector
                   , scope: ScopeId.t
                   , stmts: stmt vector
                   , sourcemap: Pos.sourcemap }

    fun updateDefTyp {pos, id, var, typ} f = {pos, id, var, typ = f typ}
    fun setDefTyp def typ' = updateDefTyp def (Fn.constantly typ')

   fun defToDoc {pos = _, id = _, var, typ} =
       Name.toDoc var <> text ":" <+> Type.Concr.toDoc typ

   val rec stmtToDoc =
       fn Val (_, def, valExpr) =>
           let val lhs = text "val" <+> defToDoc def <+> text "="
               val rhs = PPrint.align (exprToDoc valExpr)
           in lhs <> (space <> rhs <|> PPrint.nest 4 (newline <> rhs))
           end
        | Axiom (_, name, l, r) =>
           text "axiom" <+> Name.toDoc name <+> text ":"
           <+> Type.Concr.toDoc l <+> text "~" <+> Type.Concr.toDoc r
        | Expr expr => exprToDoc expr

   and stmtsToDoc =
       fn stmts => PPrint.punctuate PPrint.newline (Vector.map stmtToDoc stmts)

   and fieldToDoc =
       fn (label, expr) => Name.toDoc label <+> text "=" <+> exprToDoc expr

   and exprToDoc =
       fn Fn (_, param, arrow, body) =>
           text "\\" <> defToDoc param <+> Type.arrowDoc arrow <+> exprToDoc body
        | TFn (_, params, body) =>
           text "/\\" <> PPrint.punctuate space (Vector.map Type.defToDoc params)
               <+> text "=>" <+> exprToDoc body
        | EmptyRecord _ => text "{}"
        | With (_, _, {base, field = (label, fieldExpr)}) =>
           braces(exprToDoc base <+> text "with" <+> Name.toDoc label
                  <+> text "=" <+> exprToDoc fieldExpr)
        | Where (_, _, {base, field = (label, fieldExpr)}) =>
           braces(exprToDoc base <+> text "where" <+> Name.toDoc label
                  <+> text "=" <+> exprToDoc fieldExpr)
        | App (_, _, {callee, arg}) =>
           parens (exprToDoc callee <+> exprToDoc arg)
        | TApp (_, _, {callee, args}) =>
           parens (exprToDoc callee <+> (args |> Vector.map Type.Concr.toDoc
                                          |> PPrint.punctuate space
                                          |> brackets))
        | Field (_, _, expr, label) =>
           parens (exprToDoc expr <> text "." <> Name.toDoc label)
        | Let (_, stmts, body) =>
           text "let" <+> PPrint.align (stmtsToDoc stmts)
           <++> text "in" <+> align (exprToDoc body)
           <++> text "end"
        | Match (_, _, matchee, clauses) => let
               fun clauseToDoc {pattern, body} = patternToDoc pattern <+> text "->" <+> exprToDoc body
               in text "match" <+> exprToDoc matchee
                  <+> braces (newline <> PPrint.punctuate newline (Vector.map clauseToDoc clauses))
           end
        | Cast (_, _, expr, co) => exprToDoc expr <+> text "via" <+> Type.Co.toDoc co
        | Type (_, t) => brackets (Type.Abs.toDoc t)
        | Use (_, {var, ...}) => Name.toDoc var 
        | Const (_, c) => Const.toDoc c

    and recordToDoc =
        fn curtain => fn (_, _, fields, record) =>
            let val fieldDocs = Vector.map fieldToDoc fields
                val oneLiner = braces (punctuate (text "," <> space) fieldDocs
                                       <> (case record
                                           of SOME record =>
                                               space <> text curtain <+> exprToDoc record
                                            | NONE => PPrint.empty))
                val multiLiner =
                    align (braces (space
                                   <> punctuate (newline <> text "," <> space) fieldDocs
                                   <> (case record
                                       of SOME record =>
                                           newline <> text curtain <+> exprToDoc record
                                        | NONE => PPrint.empty)
                                   <> space))
            in oneLiner <|> multiLiner
            end

    and patternToDoc =
        fn Def (_, def) => defToDoc def
         | ConstP (_, c) => Const.toDoc c

    val exprToString = PPrint.pretty 80 o exprToDoc

    val stmtPos =
        fn Val (pos, _, _) => pos
         | Axiom (pos, _, _, _) => pos
         | Expr expr => exprPos expr

    val patPos =
        fn Def (pos, _) => pos
         | ConstP (pos, _) => pos

    fun typeFnToDoc (name, {paramKinds, kind}) =
        text "type" <+> Name.toDoc name <> text ":"
            <+> punctuate (text "," <> space) (Vector.map Type.kindToDoc paramKinds)
            <+> (if Vector.length paramKinds > 0
                 then text "->" <> space
                 else PPrint.empty)
            <> Type.kindToDoc kind

    fun axiomToDoc (name, l, r) =
        text "axiom" <+> Name.toDoc name <> text ":"
            <+> Type.Concr.toDoc l <+> text "~" <+> Type.Concr.toDoc r

    fun programToDoc {typeFns, axioms, scope = _, stmts, sourcemap = _} =
        punctuate (newline <> newline) (Vector.map typeFnToDoc typeFns)
            <++> newline <> punctuate (newline <> newline) (Vector.map axiomToDoc axioms)
            <++> newline <> stmtsToDoc stmts

    val rec typeOf =
        fn Fn (_, {typ = domain, ...}, arrow, body) =>
            Type.Arrow (arrow, {domain, codomain = typeOf body})
         | TFn (_, params, body) => Type.ForAll (params, typeOf body)
         | App (_, typ, _) | TApp (_, typ, _) => typ
         | Field (_, typ, _, _) => typ
         | Let (_, _, body) => typeOf body
         | Match (_, t, _, _) => t
         | Cast (_, t, _, _) => t
         | Type (_, t) => Type.Type t
         | Use (_, {typ, ...}) => typ
         | Const (_, c) => Type.Prim (Const.typeOf c)
end

