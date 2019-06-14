structure Cst = struct
    structure Type :> sig
        structure Prim: PRIM_TYPE where type t = PrimType.t

        datatype ('typ, 'expr) typ = Pi of Pos.t * 'typ def * 'typ
                                   | Record of Pos.t * 'typ
                                   | RowExt of Pos.t * ('typ, 'expr) row_ext
                                   | EmptyRow of Pos.t
                                   | Interface of Pos.t * 'typ decl vector
                                   | WildRow of Pos.t
                                   | Singleton of Pos.t * 'expr
                                   | Type of Pos.t
                                   | Path of 'expr
                                   | Prim of Pos.t * Prim.t

        withtype 'typ def = {var: Name.t, typ: 'typ}
        and ('typ, 'expr) row_ext = {fields: (Name.t * 'typ) vector, ext: 'typ}
        and 'typ decl = Name.t * 'typ

        val toDoc: ('typ -> PPrint.t) -> ('expr -> PPrint.t) -> ('typ, 'expr) typ -> PPrint.t
        val pos: ('expr -> Pos.t) -> ('typ, 'expr) typ -> Pos.t
    end = struct
        structure Prim = PrimType
        val op<> = PPrint.<>
        val op<+> = PPrint.<+>
        val op<++> = PPrint.<++>
        val text = PPrint.text
        val newline = PPrint.newline
        val parens = PPrint.parens
        val braces = PPrint.braces

        datatype ('typ, 'expr) typ = Pi of Pos.t * 'typ def * 'typ
                                   | Record of Pos.t * 'typ
                                   | RowExt of Pos.t * ('typ, 'expr) row_ext
                                   | EmptyRow of Pos.t
                                   | Interface of Pos.t * 'typ decl vector
                                   | WildRow of Pos.t
                                   | Singleton of Pos.t * 'expr
                                   | Type of Pos.t
                                   | Path of 'expr
                                   | Prim of Pos.t * Prim.t

        withtype 'typ def = {var: Name.t, typ: 'typ}
        and ('typ, 'expr) row_ext = {fields: (Name.t * 'typ) vector, ext: 'typ}
        and 'typ decl = Name.t * 'typ

        fun toDoc typeToDoc exprToDoc t =
            let val rec toDoc = fn Pi (_, {var, typ = domain}, codomain) =>
                                    text "fun" <+> Name.toDoc var <+> text ":" <+> typeToDoc domain
                                        <+> text "->" <+> typeToDoc codomain
                                 | Record (_, row) => braces (typeToDoc row)
                                 | RowExt (_, {fields, ext}) =>
                                    let fun fieldToDoc (label, fieldt) = 
                                            Name.toDoc label <> text ": " <> typeToDoc fieldt
                                        val fieldsDoc =
                                            PPrint.punctuate (text ", ")
                                                             (Vector.map fieldToDoc fields)
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
                                 | Type _ => text "type"
                                 | Path expr => exprToDoc expr
                                 | Prim (_, p) => Prim.toDoc p
            in toDoc t
            end

        fun pos exprPos =
            fn Pi (pos, _, _) => pos
             | Record (pos, _) => pos
             | RowExt (pos, _) => pos
             | EmptyRow pos => pos
             | WildRow pos => pos
             | Singleton (pos, _) => pos
             | Type pos => pos
             | Path expr => exprPos expr
             | Prim (pos, _) => pos
    end

    structure Term :> sig
        datatype ('typ, 'bt, 'expr, 'be) stmt = Val of Pos.t * Name.t * 'bt * 'be
                                              | Expr of 'expr
    
        and ('typ, 'bt, 'expr, 'be) expr = Fn of Pos.t * Name.t * 'bt * 'expr
                                         | Let of Pos.t * ('typ, 'bt, 'expr, 'be) stmt vector * 'expr
                                         | If of Pos.t * 'expr * 'expr * 'expr
                                         | Record of Pos.t * 'expr row
                                         | Module of Pos.t * ('typ, 'bt, 'expr, 'be) stmt vector
                                         | App of Pos.t * {callee: 'expr, arg: 'expr}
                                         | Field of Pos.t * 'expr * Name.t
                                         | Ann of Pos.t * 'expr * 'typ
                                         | Type of Pos.t * 'typ
                                         | Use of Pos.t * Name.t
                                         | Const of Pos.t * Const.t

        withtype 'expr row = {fields: (Name.t * 'expr) vector, ext: 'expr option}

        val exprPos: ('typ, 'bt, 'expr, 'be) expr -> Pos.t
        val exprToDoc: ('typ -> PPrint.t) -> ('bt -> PPrint.t) -> ('expr -> PPrint.t) -> ('be -> PPrint.t)
                        -> ('typ, 'bt, 'expr, 'be) expr -> PPrint.t
        val stmtToDoc: ('typ -> PPrint.t) -> ('bt -> PPrint.t) -> ('expr -> PPrint.t) -> ('be -> PPrint.t)
                        -> ('typ, 'bt, 'expr, 'be) stmt -> PPrint.t
    end = struct
        val op<> = PPrint.<>
        val op<+> = PPrint.<+>
        val op<++> = PPrint.<++>
        val text = PPrint.text
        val newline = PPrint.newline
        val parens = PPrint.parens
        val braces = PPrint.braces

        datatype ('typ, 'bt, 'expr, 'be) stmt = Val of Pos.t * Name.t * 'bt * 'be
                                              | Expr of 'expr
    
        and ('typ, 'bt, 'expr, 'be) expr = Fn of Pos.t * Name.t * 'bt * 'expr
                                         | Let of Pos.t * ('typ, 'bt, 'expr, 'be) stmt vector * 'expr
                                         | If of Pos.t * 'expr * 'expr * 'expr
                                         | Record of Pos.t * 'expr row
                                         | Module of Pos.t * ('typ, 'bt, 'expr, 'be) stmt vector
                                         | App of Pos.t * {callee: 'expr, arg: 'expr}
                                         | Field of Pos.t * 'expr * Name.t
                                         | Ann of Pos.t * 'expr * 'typ
                                         | Type of Pos.t * 'typ
                                         | Use of Pos.t * Name.t
                                         | Const of Pos.t * Const.t

        withtype 'expr row = {fields: (Name.t * 'expr) vector, ext: 'expr option}

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

        fun stmtToDoc typeToDoc btToDoc exprToDoc beToDoc =
            fn Val (_, name, ann, valExpr) =>
                text "val " <> Name.toDoc name <> btToDoc ann <> text " = " <> beToDoc valExpr
             | Expr expr => exprToDoc expr

        fun rowToDoc exprToDoc {fields, ext} =
            let fun entryToDoc (label, expr) = Name.toDoc label <+> text "=" <+> exprToDoc expr
                val fieldsDoc = PPrint.punctuate (text ", ") (Vector.map entryToDoc fields)
                val extDoc = Option.mapOr (fn ext => text " .." <+> exprToDoc ext) PPrint.empty ext
            in fieldsDoc <> extDoc
            end

        fun exprToDoc typeToDoc btToDoc exprToDoc beToDoc expr =
            let val stmtToDoc = stmtToDoc typeToDoc btToDoc exprToDoc beToDoc
                val rec toDoc = fn Fn (_, param, ann, body) =>
                                       text "fn" <+> Name.toDoc param <> btToDoc ann <> text " => " <> exprToDoc body
                                 | If (_, cond, conseq, alt) =>
                                    text "if" <+> exprToDoc cond
                                        <+> text "then" <+> exprToDoc conseq
                                        <+> text "else" <+> exprToDoc alt
                                    | Record (_, row) => braces (rowToDoc exprToDoc row)
                                    | Module (_, stmts) =>
                                       text "module"
                                           <> (PPrint.nest 4 (PPrint.punctuate newline (Vector.map stmtToDoc stmts)))
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
            in toDoc expr
            end
    end
end

structure FixedCst = struct
    datatype typ' = FixT of (typ', expr') Cst.Type.typ
    and expr' = Fix of (typ', typ' option, expr', expr') Cst.Term.expr

    fun typeToDoc' (FixT t) = Cst.Type.toDoc typeToDoc' exprToDoc' t
    and exprToDoc' (Fix expr) =
        let val op<+> = PPrint.<+>
            val annToDoc = Option.mapOr (fn t => PPrint.text ":" <+> typeToDoc' t) PPrint.empty
        in Cst.Term.exprToDoc typeToDoc' annToDoc exprToDoc' exprToDoc' expr 
        end

    structure Type = struct
        open Cst.Type
 
        datatype ftyp = datatype typ'
        type decl = ftyp decl
        
        val toDoc = typeToDoc'
    end

    structure Term = struct
        open Cst.Term

        datatype fexpr = datatype expr'
        
        type stmt = (Type.ftyp, Type.ftyp option, fexpr, fexpr) Cst.Term.stmt

        val exprToDoc = exprToDoc'
    end
end

