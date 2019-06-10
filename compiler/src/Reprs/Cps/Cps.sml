structure Label :> ID = Id
structure ExprId :> ID = Id

signature CPS_TYPE = sig
    structure Prim: PRIM_TYPE

    type kind = FType.kind
    type param = FType.def

    datatype typ = FnT of {typeParams: param vector, paramTypes: typ vector}
                 | TParam of param
                 | Prim of Prim.t

    val int: typ
    val cont: typ -> typ

    val toDoc: typ -> PPrint.t
end

signature CPS_TERM = sig
    type typ
    type param = {var: Name.t, typ: typ}

    datatype oper = PrimApp of primapp
                  | Param of param
                  | Label of Label.t
                  | Const of Const.t
    and primapp = IAdd of expr * expr
    withtype expr = {id: ExprId.t, oper: oper}

    datatype transfer = Goto of expr * typ vector * expr vector
                      | If of expr * expr * expr 

    val newExpr: oper -> expr

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

signature CPS_PROGRAM = sig
    type cont
    type program

    val toDoc: program -> PPrint.t
    val findCont: program * Label.t -> cont option

    (* TODO: new: unit -> t, build: t * Label.t * cont -> program *)
    structure Builder: sig
        type t
        
        val new: Label.t -> t
        val insertCont: t * Label.t * cont -> unit
        val build: t -> program
    end
end

structure Cps :> sig
    structure Type: CPS_TYPE where type Prim.t = PrimType.t
    structure Term: CPS_TERM where type typ = Type.typ
    structure Cont: CPS_CONT where
        type Type.typ = Type.typ
        and type Term.typ = Type.typ
        and type Term.transfer = Term.transfer
    structure Program: CPS_PROGRAM where type cont = Cont.cont
end = struct
    val text = PPrint.text
    val space = PPrint.space
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>

    fun optionalArgs delims argDocs =
        if Vector.length argDocs > 0
        then delims (PPrint.punctuate (text "," <> space) argDocs)
        else PPrint.empty

    structure Type = struct
        structure Prim = FType.Prim

        type kind = FType.kind

        type param = FType.def

        datatype typ = FnT of {typeParams: param vector, paramTypes: typ vector}
                     | TParam of param
                     | Prim of Prim.t

        val int = Prim Prim.I32
        
        fun cont paramTyp = FnT { typeParams = Vector.fromList []
                                , paramTypes = Vector.fromList [paramTyp] }

        val paramToDoc = FType.defToDoc

        val rec toDoc =
            fn FnT {typeParams, paramTypes} =>
                let val tDocs = Vector.map paramToDoc typeParams
                    val vDocs = Vector.map toDoc paramTypes
                in text "fn" <+> optionalArgs PPrint.brackets tDocs
                             <+> optionalArgs PPrint.parens vDocs
                end
             | TParam {var, kind = _} => Name.toDoc var
             | Prim p => Prim.toDoc p
    end

    structure Term = struct
        type typ = Type.typ

        type id = word

        type param = {var: Name.t, typ: Type.typ}

        datatype oper = PrimApp of primapp
                      | Param of param 
                      | Label of Label.t
                      | Const of Const.t

        and primapp = IAdd of expr * expr

        withtype expr = {id: ExprId.t, oper: oper}

        datatype transfer = Goto of expr * Type.typ vector * expr vector
                          | If of expr * expr * expr

        fun newExpr oper = {id = ExprId.fresh (), oper}
        fun foldChildren f acc {oper, ...} =
            case oper
            of PrimApp (IAdd (l, r)) => f (r, f (l, acc))
             | Param _ | Label _ | Const _ => acc

        fun foldTransferExprs f acc =
            fn Goto (dest, _, vArgs) => Vector.foldl f (f (dest, acc)) vArgs
             | If (cond, conseq, alt) => f (alt, f (conseq, f (cond, acc)))

        fun paramToDoc {var, typ} = Name.toDoc var <> text ":" <+> Type.toDoc typ

        fun exprToIdDoc {id, oper = _} = text "#" <> ExprId.toDoc id

        val primappToDoc =
            fn oper as IAdd (l, r) =>
                text "iadd" <+> exprToIdDoc l <> text "," <+> exprToIdDoc r

        val operToDoc =
            fn PrimApp papp => PPrint.parens (primappToDoc papp)
             | Param {var, ...} => Name.toDoc var
             | Label label => text "$" <> Label.toDoc label
             | Const c => Const.toDoc c

        fun exprToDoc visited (expr as {id, oper}) =
            let val childrenDoc =
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
                       of Goto (dest, tArgs, vArgs) =>
                           (* FIXME: Get `name` from cont in program: *)
                           let val destDoc = exprToIdDoc dest
                               val tDocs = Vector.map Type.toDoc tArgs
                               val vDocs = Vector.map exprToIdDoc vArgs
                           in destDoc <> optionalArgs PPrint.brackets tDocs
                                      <> optionalArgs PPrint.parens vDocs
                           end 
                        | If (cond, conseq, alt) =>
                           text "if" <+> exprToIdDoc cond
                               <+> text "then" <+> exprToIdDoc conseq
                               <+> text "else" <+> exprToIdDoc alt)
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
                <> optionalArgs PPrint.brackets (Vector.map Type.paramToDoc typeParams)
                <> optionalArgs PPrint.parens (Vector.map Term.paramToDoc valParams)
                <+> PPrint.lBrace
                <> PPrint.nest 4 (PPrint.newline <> Term.transferToDoc visited body)
                <++> PPrint.rBrace
    end

    structure Program = struct
        type cont = Cont.cont
        type program = {conts: Cont.cont Label.SortedMap.map, start: Label.t}

        fun toDoc {conts, start} =
            let val visited = ExprId.HashSet.mkEmpty 0
                val step = fn (label, cont, SOME acc) => 
                               SOME (acc <++> PPrint.newline <> Label.toDoc label <+> text "=" <+> Cont.toDoc visited cont)
                            | (label, cont, NONE) =>
                               SOME (Label.toDoc label <+> text "=" <+> Cont.toDoc visited cont)
            in getOpt (Label.SortedMap.foldli step NONE conts, PPrint.empty)
            end

        fun findCont ({conts, start = _}, label) = Label.SortedMap.find (conts, label)

        structure Builder = struct
            type t = {conts: cont Label.SortedMap.map ref, start: Label.t}

            fun new start = {conts = ref Label.SortedMap.empty, start}

            fun insertCont ({conts, start = _}, label, cont) =
                conts := Label.SortedMap.insert (!conts, label, cont)
            
            fun build {conts, start} = {conts = !conts, start}
        end
    end
end

