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

    datatype expr = PrimApp of primapp
                  | Param of param 
                  | Const of Const.t
    and primapp = IAdd of expr * expr

    datatype transfer = Goto of label * typ vector * expr vector
                      | If of expr * label * label

    val exprToDoc: expr -> PPrint.t
    val transferToDoc: transfer -> PPrint.t
end

signature CPS_CONT = sig
    structure Type: CPS_TYPE
    structure Term: CPS_TERM

    type cont = { name: Name.t
                , typeParams: Type.param vector
                , valParams: Term.param vector
                , body: Term.transfer }
end

functor Cps (WordSortedMap: ORD_MAP where type Key.ord_key = word) :> sig
    structure Type: CPS_TYPE
    structure Term: CPS_TERM where type typ = Type.typ
    structure Cont: CPS_CONT

    type program
end = struct
        val text = PPrint.text
        val space = PPrint.space
        val op<> = PPrint.<>
        val op<+> = PPrint.<+>

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

        type param = {var: Name.t, typ: Type.typ}

        datatype expr = PrimApp of primapp
                      | Param of param 
                      | Const of Const.t

        and primapp = IAdd of expr * expr

        datatype transfer = Goto of label * Type.typ vector * expr vector
                          | If of expr * label * label

        fun paramToDoc {var, typ} = Name.toDoc var <> text ":" <+> Type.toDoc typ

        (* TODO: express sharing in the graph in the printout *)
        val rec exprToDoc =
            fn PrimApp papp => PPrint.parens (primappToDoc papp)
             | Param {var, ...} => Name.toDoc var
             | Const c => Const.toDoc c

        and primappToDoc =
            fn IAdd (l, r) => text "iadd" <+> exprToDoc l <> text "," <+> exprToDoc r

        val transferToDoc =
            fn Goto (label, tArgs, vArgs) =>
                (* FIXME: Get `name` from cont in program: *)
                let val name = Name.freshen (Name.fromString (Word.toString label))
                    val tDocs = Vector.map Type.toDoc tArgs
                    val vDocs = Vector.map exprToDoc vArgs
                in Name.toDoc name <> PPrint.brackets (PPrint.punctuate (text "," <> space) tDocs)
                                   <> PPrint.parens (PPrint.punctuate (text "," <> space) vDocs)
                end 
             | If (cond, conseq, alt) => text "if" <+> exprToDoc cond
                                                   <+> text "then" <+> PPrint.word conseq 
                                                   <+> text "else" <+> PPrint.word alt
    end

    structure Cont = struct
        structure Type = Type
        structure Term = Term

        type cont = { name: Name.t
                    , typeParams: Type.param vector
                    , valParams: Term.param vector
                    , body: Term.transfer }
    end

    type program = Cont.cont WordSortedMap.map
end

