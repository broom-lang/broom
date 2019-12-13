structure CpsId = struct
    structure Super = Id(struct end)
    open Super
structure SortedSet = BinarySetFn(OrdKey) structure HashSetMut = HashSetFn(HashKey) end signature CPS_TYPE = sig structure Prim : PRIM_TYPE 
    type param = FType.def
    
    datatype t
        = FnT of {tDomain : param vector, vDomain : t vector, codomain : t}
        | TParam of param
        | Prim of Prim.t

    val toDoc : t -> PPrint.t
end

signature CPS_TERM = sig
    structure Type : CPS_TYPE

    type def = CpsId.t

    structure Transfer : sig
        datatype pat
            = AnyP
            | ConstP of Const.t

        datatype t
            = Goto of {callee : def, tArgs : Type.t vector, vArgs : def vector}
            | Match of def * {pattern : pat, target : def} vector

        val toDoc : t -> PPrint.t
    end

    structure Expr : sig
        structure ParentMap : HASH_MAP where type key = def option

        datatype oper
            = Fn of { name : Name.t option
                    , tParams : Type.param vector, vParams : Type.t vector
                    , body : Transfer.t }
            | PrimApp of {opn : Primop.t, tArgs : Type.t vector, vArgs : def vector}
            | Param of def * int
            | Const of Const.t

        type t = {parent : def option, oper : oper}

        val toDoc : t -> PPrint.t

        val foldDefs : (CpsId.t * 'a -> 'a) -> 'a -> oper -> 'a
    end
end

signature CPS_PROGRAM = sig
    structure Term : CPS_TERM

    structure Map : HASH_MAP where type key = Term.def

    type t = {typeFns : FType.def vector, stmts : Term.Expr.t Map.t, main : Term.def}

    val byParent : t -> CpsId.SortedSet.set Term.Expr.ParentMap.t

    val toDoc : t -> PPrint.t
end

structure Cps :> sig
    structure Type : CPS_TYPE
    structure Term : CPS_TERM where type Type.t = Type.t
    structure Program : CPS_PROGRAM where type Term.Expr.oper = Term.Expr.oper
end = struct
    structure DefSet = CpsId.SortedSet
    structure DefSetMut = CpsId.HashSetMut

    val text = PPrint.text
    val space = PPrint.space
    val newline = PPrint.newline
    val comma = PPrint.comma
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>
    val parens = PPrint.parens
    val brackets = PPrint.brackets
    val punctuate = PPrint.punctuate
    val nest = PPrint.nest

    structure Type = struct
        structure Prim = PrimType

        type param = FType.def
        
        datatype t
            = FnT of {tDomain : param vector, vDomain : t vector, codomain : t}
            | TParam of param
            | Prim of Prim.t

        val rec toDoc =
            fn FnT {tDomain, vDomain, codomain} =>
                text "fn"
                <+> brackets (punctuate (comma <> space) (Vector.map FType.defToDoc tDomain))
                <+> parens (punctuate (comma <> space) (Vector.map toDoc vDomain))
                <+> text "->" <+> toDoc codomain
             | TParam {var, ...} => text (FType.Id.toString var)
             | Prim p => Prim.toDoc p
    end

    structure Term = struct
        structure Type = Type

        type def = CpsId.t

        structure Transfer = struct
            datatype pat
                = AnyP
                | ConstP of Const.t

            datatype t
                = Goto of {callee : def, tArgs : Type.t vector, vArgs : def vector}
                | Match of def * {pattern : pat, target : def} vector

            val patToDoc =
                fn AnyP => text "_"
                 | ConstP c => Const.toDoc c

            fun clauseToDoc {pattern, target} =
                patToDoc pattern <+> text "->" <+> CpsId.toDoc target

            val toDoc =
                fn Goto {callee, tArgs, vArgs} =>
                    CpsId.toDoc callee
                    <+> brackets (punctuate (comma <> space) (Vector.map Type.toDoc tArgs))
                    <+> parens (punctuate (comma <> space) (Vector.map CpsId.toDoc vArgs))
                 | Match (matchee, clauses) =>
                    text "match" <+> CpsId.toDoc matchee
                    <> nest 4 (newline <> (punctuate newline (Vector.map clauseToDoc clauses)))
        end

        structure Expr = struct
            structure ParentMap = HashMap(struct
                type hash_key = def option

                val hashVal = Option.hash CpsId.hash
                val sameKey = op=
                val toString =
                    fn SOME def => CpsId.toString def
                     | NONE => "-"
            end)

            datatype oper
                = Fn of { name : Name.t option
                        , tParams : Type.param vector, vParams : Type.t vector
                        , body : Transfer.t }
                | PrimApp of {opn : Primop.t, tArgs : Type.t vector, vArgs : def vector}
                | Param of def * int
                | Const of Const.t

            type t = {parent : def option, oper : oper}

            fun foldDefs f acc =
                fn Fn _ => acc
                 | PrimApp {opn = _, tArgs = _, vArgs} => Vector.foldl f acc vArgs
                 | Param _ => acc
                 | Const _ => acc

            val operToDoc =
                fn Fn {name, ...} => text "fn" <+> Option.mapOr Name.toDoc PPrint.empty name
                 | PrimApp {opn, tArgs, vArgs} =>
                    Primop.toDoc opn
                    <+> brackets (punctuate (comma <> space) (Vector.map Type.toDoc tArgs))
                    <+> parens (punctuate (comma <> space) (Vector.map CpsId.toDoc vArgs))
                 | Param (def, i) => text "param" <+> CpsId.toDoc def <+> PPrint.int i
                 | Const c => Const.toDoc c

            fun toDoc {parent = _, oper} = operToDoc oper
        end
    end

    structure Program = struct
        structure Term = Term
        structure ParentMap = Term.Expr.ParentMap

        structure Map = HashMap(struct
            open CpsId.HashKey

            val toString = CpsId.toString
        end)

        type t = {typeFns : FType.def vector, stmts : Term.Expr.t Map.t, main : Term.def}

        fun byParent ({stmts, ...}: t) =
            let fun step ((def, {parent, ...}), acc) =
                    case ParentMap.find acc parent
                    of SOME vs => ParentMap.insert acc (parent, DefSet.add (vs, def))
                     | NONE => ParentMap.insert acc (parent, DefSet.singleton def)
            in Map.fold step ParentMap.empty stmts
            end

        fun fnToDoc ({stmts, ...} : t) visited fnDef fnExprs =
            let fun depsToDoc oper =
                    Term.Expr.foldDefs (fn (depDef, acc) => acc <++> stmtToDoc depDef)
                                       PPrint.empty oper

                and stmtToDoc def =
                    if not (DefSet.member (fnExprs, def))
                       orelse DefSetMut.member (visited, def)
                    then PPrint.empty
                    else let do DefSetMut.add (visited, def)
                             val {parent = _, oper} = Map.lookup stmts def
                         in depsToDoc oper
                            <++> CpsId.toDoc def <+> text "=" <+> Term.Expr.operToDoc oper
                         end

                val {parent = _, oper = Term.Expr.Fn {name, tParams, vParams, body}} = Map.lookup stmts fnDef
            in CpsId.toDoc fnDef <+> text "=" <+> text "fn"
               <> Option.mapOr (fn name => space <> Name.toDoc name) PPrint.empty name
               <+> brackets (punctuate (comma <> space) (Vector.map FType.defToDoc tParams))
               <+> parens (punctuate (comma <> space) (Vector.map Type.toDoc vParams))
               <> nest 4 (newline
                          <> DefSet.foldl (fn (def, acc) => acc <++> stmtToDoc def) PPrint.empty fnExprs
                          <++> Term.Transfer.toDoc body)
            end

        (* FIXME: Handle parent = NONE case (before all the others): *)
        fun stmtsToDoc program =
            let val visited = DefSetMut.mkEmpty 0
            in ParentMap.fold (fn ((SOME fnDef, fnExprs), acc) =>
                                   acc <++> fnToDoc program visited fnDef fnExprs)
                              PPrint.empty (byParent program)
            end

        fun typeFnToDoc def = text "type" <+> FType.defToDoc def

        (* TODO: Nest functions in output: *)
        fun toDoc (program as {typeFns, stmts = _, main}) =
            punctuate newline (Vector.map typeFnToDoc typeFns)
            <++> stmtsToDoc program
            <++> text "entry" <+> CpsId.toDoc main
    end
end

