signature FAST_TERM = sig
    structure Type: CLOSED_FAST_TYPE

    type def = {var: Name.t, typ: Type.concr}

    datatype expr
        = Fn of Pos.t * def * expr
        | TFn of Pos.t * Type.def vector * expr
        | Extend of Pos.t * Type.concr * (Name.t * expr) vector * expr option
        | Override of Pos.t * Type.concr * (Name.t * expr) vector * expr
        | App of Pos.t * Type.concr * {callee: expr, arg: expr}
        | TApp of Pos.t * Type.concr * {callee: expr, args: Type.concr vector}
        | Field of Pos.t * Type.concr * expr * Name.t
        | Let of Pos.t * stmt vector * expr
        | If of Pos.t * expr * expr * expr
        | Cast of Pos.t * expr * Type.co
        | Type of Pos.t * Type.abs
        | Use of Pos.t * def
        | Const of Pos.t * Const.t

    and stmt
        = Val of Pos.t * def * expr
        | Expr of expr

    type program = { typeFns: (Name.t * Type.tfn_sig) vector
                   , axioms: (Name.t * Type.concr * Type.concr) vector
                   , body: expr }

    val exprPos: expr -> Pos.t
    val exprToDoc: expr -> PPrint.t
    val exprToString: expr -> string
    val stmtPos: stmt -> Pos.t
    val stmtToDoc: stmt -> PPrint.t
    val stmtsToDoc: stmt vector -> PPrint.t
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

    type def = {var: Name.t, typ: Type.concr}

    datatype expr
        = Fn of Pos.t * def * expr
        | TFn of Pos.t * Type.def vector * expr
        | Extend of Pos.t * Type.concr  * (Name.t * expr) vector * expr option
        | Override of Pos.t * Type.concr * (Name.t * expr) vector * expr
        | App of Pos.t * Type.concr * {callee: expr, arg: expr}
        | TApp of Pos.t * Type.concr * {callee: expr, args: Type.concr vector}
        | Field of Pos.t * Type.concr * expr * Name.t
        | Let of Pos.t * stmt vector * expr
        | If of Pos.t * expr * expr * expr
        | Cast of Pos.t * expr * Type.co
        | Type of Pos.t * Type.abs
        | Use of Pos.t * def
        | Const of Pos.t * Const.t

    and stmt
        = Val of Pos.t * def * expr
        | Expr of expr

    val exprPos =
        fn Fn (pos, _, _) => pos
         | TFn (pos, _, _) => pos
         | Extend (pos, _, _, _) => pos
         | Override (pos, _, _, _) => pos
         | App (pos, _, _) => pos
         | TApp (pos, _, _) => pos
         | Field (pos, _, _, _) => pos
         | Let (pos, _, _) => pos
         | If (pos, _, _, _) => pos
         | Type (pos, _) => pos
         | Use (pos, _) => pos
         | Const (pos, _) => pos

    type program = { typeFns: (Name.t * Type.tfn_sig) vector
                   , axioms: (Name.t * Type.concr * Type.concr) vector
                   , body: expr }

   fun defToDoc {var, typ} = Name.toDoc var <> text ":" <+> Type.Concr.toDoc typ

   val rec stmtToDoc =
       fn Val (_, def, valExpr) =>
           let val lhs = text "val" <+> defToDoc def <+> text "="
               val rhs = PPrint.align (exprToDoc valExpr)
           in lhs <> (space <> rhs <|> PPrint.nest 4 (newline <> rhs))
           end
        | Expr expr => exprToDoc expr

   and stmtsToDoc =
       fn stmts => PPrint.punctuate PPrint.newline (Vector.map stmtToDoc stmts)

   and fieldToDoc =
       fn (label, expr) => Name.toDoc label <+> text "=" <+> exprToDoc expr

   and exprToDoc =
       fn Fn (_, param, body) =>
           text "\\" <> defToDoc param <+> text "=>" <+> exprToDoc body
        | TFn (_, params, body) =>
           text "/\\" <> PPrint.punctuate space (Vector.map Type.defToDoc params)
               <+> text "=>" <+> exprToDoc body
        | Extend args => recordToDoc "extending" args
        | Override (pos, typ, fields, ext) => recordToDoc "overriding" (pos, typ, fields, SOME ext)
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
        | If (_, cond, conseq, alt) =>
           text "if" <+> exprToDoc cond
               <+> text "then" <+> exprToDoc conseq
               <+> text "else" <+> exprToDoc alt
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

    val exprToString = PPrint.pretty 80 o exprToDoc

    val stmtPos =
        fn Val (pos, _, _) => pos
         | Expr expr => exprPos expr

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

    fun programToDoc {typeFns, axioms, body} =
        punctuate (newline <> newline) (Vector.map typeFnToDoc typeFns)
            <++> newline <> punctuate (newline <> newline) (Vector.map axiomToDoc axioms)
            <++> newline <> exprToDoc body

    val rec typeOf =
        fn Fn (pos, {typ = domain, ...}, body) => Type.Arrow (pos, {domain, codomain = typeOf body})
         | TFn (pos, params, body) => Type.ForAll (pos, params, typeOf body)
         | Extend (_, typ, _, _) | Override (_, typ, _, _) | App (_, typ, _) | TApp (_, typ, _) => typ
         | Field (_, typ, _, _) => typ
         | Let (_, _, body) => typeOf body
         | If (_, _, conseq, _) => typeOf conseq
         | Type (pos, t) => Type.Type (pos, t)
         | Use (_, {typ, ...}) => typ
         | Const (pos, c) => Type.Prim (pos, Const.typeOf c)
end

