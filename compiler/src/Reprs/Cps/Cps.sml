structure Label :> ID = Id
structure ExprId :> ID = Id

signature CPS_TYPE = sig
    structure Prim: PRIM_TYPE

    type kind = FType.kind
    type param = FType.def

    datatype typ = FnT of {typeParams: param vector, paramTypes: typ vector}
                 | TParam of param
                 | Prim of Prim.t

    val toDoc: typ -> PPrint.t
end

signature CPS_TERM = sig
    type typ
    type label
    type param = {var: Name.t, typ: typ}

    datatype oper = PrimApp of primapp
                  | Param of param
                  | Label of label
                  | Const of Const.t
    and primapp = IAdd of expr * expr
    withtype expr = {id: ExprId.t, oper: oper}

    datatype transfer = Goto of label * typ vector * expr vector
                      | If of expr * label * label

    val foldChildren: (expr * 'a -> 'a) -> 'a -> expr -> 'a
    val foldTransferExprs: (expr * 'a -> 'a) -> 'a -> transfer -> 'a

    val exprToDoc: ExprId.HashSet.set -> expr -> PPrint.t
    val transferToDoc: ExprId.HashSet.set -> transfer -> PPrint.t
end

signature CPS_CONT = sig
    structure Type: CPS_TYPE
    structure Term: CPS_TERM

    type cont = { name: Name.t
                , typeParams: Type.param vector
                , valParams: Term.param vector
                , body: Term.transfer }

    val toDoc: ExprId.HashSet.set -> cont -> PPrint.t
end

structure Cps :> sig
    structure Type: CPS_TYPE
    structure Term: CPS_TERM where type typ = Type.typ
    structure Cont: CPS_CONT

    type program

    val programToDoc: program -> PPrint.t
    val insertCont: program * Label.t * Cont.cont -> program
    val findCont: program * Label.t -> Cont.cont option
end = struct
    val text = PPrint.text
    val space = PPrint.space
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>

    structure Type = struct
        structure Prim = FType.Prim

        type kind = FType.kind

        type param = FType.def

        datatype typ = FnT of {typeParams: param vector, paramTypes: typ vector}
                     | TParam of param
                     | Prim of Prim.t

        val paramToDoc = FType.defToDoc

        val rec toDoc =
            fn FnT {typeParams, paramTypes} =>
                let val tDocs = Vector.map paramToDoc typeParams
                    val vDocs = Vector.map toDoc paramTypes
                in text "fn" <+> PPrint.brackets (PPrint.punctuate (text "," <> space) tDocs)
                             <+> PPrint.parens (PPrint.punctuate (text "," <> space) vDocs)
                end
    end

    structure Term = struct
        type typ = Type.typ

        type label = word

        type id = word

        type param = {var: Name.t, typ: Type.typ}

        datatype oper = PrimApp of primapp
                      | Param of param 
                      | Label of label
                      | Const of Const.t

        and primapp = IAdd of expr * expr

        withtype expr = {id: ExprId.t, oper: oper}

        datatype transfer = Goto of label * Type.typ vector * expr vector
                          | If of expr * label * label

        fun foldChildren f acc {oper, ...} =
            case oper
            of PrimApp (IAdd (l, r)) => f (r, f (l, acc))
             | Param _ | Label _ | Const _ => acc

        fun foldTransferExprs f acc =
            fn Goto (_, _, vArgs) => Vector.foldl f acc vArgs
             | If (cond, _, _) => f (cond, acc)

        fun paramToDoc {var, typ} = Name.toDoc var <> text ":" <+> Type.toDoc typ

        fun exprToDoc visited (expr as {id, oper}) =
            let val primappToDoc =
                    fn oper as IAdd ({id = lid, ...}, {id = rid, ...}) =>
                        text "iadd" <+> ExprId.toDoc lid <> text "," <+> ExprId.toDoc rid

                val operToDoc =
                    fn PrimApp papp => PPrint.parens (primappToDoc papp)
                     | Param {var, ...} => Name.toDoc var
                     | Label label => text "fn" <+> PPrint.word label
                     | Const c => Const.toDoc c

                val childrenDoc =
                    foldChildren (fn (child, SOME acc) =>
                                      SOME (acc <++> exprToDoc visited child)
                                   | (child, NONE) => SOME (exprToDoc visited child))
                                 NONE expr
            in if ExprId.HashSet.member (visited, id)
               then getOpt (childrenDoc, PPrint.empty)
               else ( ExprId.HashSet.add (visited, id)
                    ; Option.mapOr (fn cdoc => cdoc <> PPrint.newline) PPrint.empty childrenDoc
                          <> ExprId.toDoc id <+> text "=" <+> operToDoc oper )
            end

        fun transferToDoc visited transfer =
            let val exprsDoc =
                    foldTransferExprs (fn (expr, SOME acc) =>
                                           SOME (acc <++> exprToDoc visited expr)
                                        | (expr, NONE) => SOME (exprToDoc visited expr))
                                      NONE transfer
            in Option.mapOr (fn doc => doc <> PPrint.newline) PPrint.empty exprsDoc
                   <> (case transfer
                       of Goto (label, tArgs, vArgs) =>
                           (* FIXME: Get `name` from cont in program: *)
                           let val name = Name.freshen (Name.fromString (Word.toString label))
                               val tDocs = Vector.map Type.toDoc tArgs
                               val vDocs = Vector.map (ExprId.toDoc o #id) vArgs
                           in Name.toDoc name <> PPrint.brackets (PPrint.punctuate (text "," <> space) tDocs)
                                              <> PPrint.parens (PPrint.punctuate (text "," <> space) vDocs)
                           end 
                        | If ({id, ...}, conseq, alt) => text "if" <+> ExprId.toDoc id
                                                             <+> text "then" <+> PPrint.word conseq 
                                                             <+> text "else" <+> PPrint.word alt)
            end
    end

    structure Cont = struct
        structure Type = Type
        structure Term = Term

        type cont = { name: Name.t
                    , typeParams: Type.param vector
                    , valParams: Term.param vector
                    , body: Term.transfer }

        fun toDoc visited {name, typeParams, valParams, body} =
            text "fn" <+> Name.toDoc name
                <> PPrint.brackets (PPrint.punctuate (text "," <> space)
                                                     (Vector.map Type.paramToDoc typeParams))
                <> PPrint.parens (PPrint.punctuate (text "," <> space)
                                                   (Vector.map Type.paramToDoc typeParams))
                <+> PPrint.lBrace
                <> PPrint.nest 4 (PPrint.newline <> Term.transferToDoc visited body)
                <++> PPrint.rBrace
    end

    type program = Cont.cont Label.SortedMap.map

    fun programToDoc program =
        let val visited = ExprId.HashSet.mkEmpty 0
            val step = fn (cont, SOME acc) => SOME (acc <++> Cont.toDoc visited cont)
                        | (cont, NONE) => SOME (Cont.toDoc visited cont)
        in getOpt (Label.SortedMap.foldl step NONE program, PPrint.empty)
        end

    val insertCont = Label.SortedMap.insert
    val findCont = Label.SortedMap.find
end

