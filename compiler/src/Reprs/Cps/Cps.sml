structure CpsId = struct
    structure Super = Id(struct end)
    open Super

    fun toDoc id = PPrint.<> (PPrint.text "%", Super.toDoc id)
    
    structure SortedSet = BinarySetFn(OrdKey)
    structure HashSetMut = HashSetFn(HashKey)
end

structure Label = struct
    structure Super = Id(struct end)
    open Super

    fun toDoc id = PPrint.<> (PPrint.text "$", Super.toDoc id)
    
    structure SortedSet = BinarySetFn(OrdKey)
    structure HashSetMut = HashSetFn(HashKey)
end

signature CPS_TYPE = sig
    structure Prim : PRIM_TYPE where type t = PrimType.t

    type param = FType.def
    
    datatype t
        = FnT of {tDomain : param vector, vDomain : t vector}
        | Record of t
        | EmptyRow
        | StackT
        | Type of t
        | TParam of param
        | Prim of Prim.t

    val toDoc : t -> PPrint.t
end

signature CPS_EXPR = sig
    structure Type : CPS_TYPE

    type def = CpsId.t

    structure ParentMap : HASH_MAP where type key = Label.t option

    datatype oper
        = PrimApp of {opn : Primop.t, tArgs : Type.t vector, vArgs : def vector}
        | EmptyRecord
        | With of {base : def, field : Name.t * def}
        | Where of {base : def, field : Name.t * def}
        | Without of {base : def, field : Name.t}
        | Field of def * Name.t
        | Type of Type.t
        | Label of Label.t
        | Param of Label.t * int
        | Const of Const.t

    type t = {parent : Label.t option, oper : oper}

    val toDoc : t -> PPrint.t

    val foldDeps : (CpsId.t * 'a -> 'a) -> 'a -> oper -> 'a
end

signature CPS_CONT = sig
    structure Type : CPS_TYPE

    structure Transfer : sig
        type def = CpsId.t

        datatype pat
            = AnyP
            | ConstP of Const.t

        datatype t
            = Goto of {callee : def, tArgs : Type.t vector, vArgs : def vector}
            | Match of def * {pattern : pat, target : def} vector

        val toDoc : t -> PPrint.t
    end

    type t =
        { name : Name.t option
        , tParams : Type.param vector, vParams : Type.t vector
        , body : Transfer.t }

    val toDoc : t -> PPrint.t
end

signature CPS_PROGRAM = sig
    structure Expr : CPS_EXPR
    structure Cont : CPS_CONT

    structure Map : HASH_MAP where type key = Expr.def
    structure LabelMap : HASH_MAP where type key = Label.t

    (* TODO: Make abstract? *)
    type t =
        { typeFns : FType.def vector
        , stmts : Expr.t Map.t
        , conts : Cont.t LabelMap.t
        , main : Label.t }

    val byParent : t -> CpsId.SortedSet.set Expr.ParentMap.t

    val toDoc : t -> PPrint.t

    structure Builder : sig
        type builder

        val new : FType.def vector -> builder
        val insertCont : builder -> Label.t * Cont.t -> unit
        val express : builder -> Expr.t -> Expr.def
        val build : builder -> Label.t -> t
    end
end

structure Cps :> sig
    structure Type : CPS_TYPE
    structure Expr : CPS_EXPR where type Type.t = Type.t
    structure Cont : CPS_CONT where type Type.t = Type.t
    structure Program : CPS_PROGRAM
        where type Expr.Type.t = Type.t
        where type Expr.oper = Expr.oper
        where type Cont.Type.t = Cont.Type.t
        where type Cont.Transfer.t = Cont.Transfer.t
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
    val braces = PPrint.braces
    val punctuate = PPrint.punctuate
    val nest = PPrint.nest

    structure Type = struct
        structure Prim = PrimType

        type param = FType.def
        
        datatype t
            = FnT of {tDomain : param vector, vDomain : t vector}
            | Record of t
            | EmptyRow
            | StackT
            | Type of t
            | TParam of param
            | Prim of Prim.t

        val rec toDoc =
            fn FnT {tDomain, vDomain} =>
                text "fn"
                <+> brackets (punctuate (comma <> space) (Vector.map FType.defToDoc tDomain))
                <+> parens (punctuate (comma <> space) (Vector.map toDoc vDomain))
             | Record row => braces (toDoc row)
             | EmptyRow => PPrint.empty
             | StackT => text "__stack"
             | Type t => brackets (text "=" <+> toDoc t)
             | TParam {var, ...} => text ("g__" ^ FType.Id.toString var) (* HACK: g__ *)
             | Prim p => Prim.toDoc p
    end

    structure Cont = struct
        structure Type = Type

        structure Transfer = struct
            type def = CpsId.t

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
                    text "goto" <+> CpsId.toDoc callee
                    <+> brackets (punctuate (comma <> space) (Vector.map Type.toDoc tArgs))
                    <+> parens (punctuate (comma <> space) (Vector.map CpsId.toDoc vArgs))
                 | Match (matchee, clauses) =>
                    text "match" <+> CpsId.toDoc matchee
                    <> nest 4 (newline <> (punctuate newline (Vector.map clauseToDoc clauses)))
        end

        type t =
            { name : Name.t option
            , tParams : Type.param vector, vParams : Type.t vector
            , body : Transfer.t }

        fun toDoc {name, tParams, vParams, body} =
            text "fn"
            <> (case name
                of SOME name => space <> Name.toDoc name
                 | NONE => PPrint.empty)
            <+> brackets (punctuate (comma <> space) (Vector.map FType.defToDoc tParams))
            <+> parens (punctuate (comma <> space) (Vector.map Type.toDoc vParams))
            <> nest 4 (newline <> Transfer.toDoc body)
    end

    structure Expr = struct
        structure Type = Type

        type def = CpsId.t

        structure ParentMap = HashMap(struct
            type hash_key = Label.t option

            val hashVal = Option.hash Label.hash
            val sameKey = op=
            val toString =
                fn SOME def => Label.toString def
                 | NONE => "-"
        end)

        datatype oper
            = PrimApp of {opn : Primop.t, tArgs : Type.t vector, vArgs : def vector}
            | EmptyRecord
            | With of {base : def, field : Name.t * def}
            | Where of {base : def, field : Name.t * def}
            | Without of {base : def, field : Name.t}
            | Field of def * Name.t
            | Type of Type.t
            | Label of Label.t
            | Param of Label.t * int
            | Const of Const.t

        type t = {parent : Label.t option, oper : oper}

        fun foldDeps f acc =
            fn PrimApp {opn = _, tArgs = _, vArgs} => Vector.foldl f acc vArgs
             | With {base, field = (_, fielde)} => f (fielde, f (base, acc))
             | Where {base, field = (_, fielde)} => f (fielde, f (base, acc))
             | Without {base, field = _} => f (base, acc)
             | Field (expr, _) => f (expr, acc)
             | EmptyRecord => acc
             | Type _ => acc
             | Label _ => acc
             | Param _ => acc
             | Const _ => acc

        val operToDoc =
            fn PrimApp {opn, tArgs, vArgs} =>
                Primop.toDoc opn
                <+> brackets (punctuate (comma <> space) (Vector.map Type.toDoc tArgs))
                <+> parens (punctuate (comma <> space) (Vector.map CpsId.toDoc vArgs))
             | EmptyRecord => braces PPrint.empty
             | With {base, field = (label, fielde)} =>
                CpsId.toDoc base <+> text "with"
                <+> Name.toDoc label <+> text "=" <+> CpsId.toDoc fielde
             | Where {base, field = (label, fielde)} =>
                CpsId.toDoc base <+> text "where"
                <+> Name.toDoc label <+> text "=" <+> CpsId.toDoc fielde
             | Without {base, field} =>
                CpsId.toDoc base <+> text "without" <+> Name.toDoc field
             | Field (expr, label) => CpsId.toDoc expr <+> text "." <+> Name.toDoc label
             | Type t => brackets (Type.toDoc t)
             | Label label => text "fn" <+> Label.toDoc label
             | Param (label, i) => text "param" <+> Label.toDoc label <+> PPrint.int i
             | Const c => text "const" <+> Const.toDoc c

        fun toDoc {parent = _, oper} = operToDoc oper
    end

    structure Program = struct
        structure Expr = Expr
        structure ParentMap = Expr.ParentMap
        structure Cont = Cont

        structure Map = HashMap(struct
            open CpsId.HashKey

            val toString = CpsId.toString
        end)

        structure LabelMap = HashMap(struct
            open Label.HashKey

            val toString = Label.toString
        end)

        type t =
            { typeFns : FType.def vector
            , stmts : Expr.t Map.t
            , conts : Cont.t LabelMap.t
            , main : Label.t }

        fun byParent ({stmts, ...}: t) =
            let fun step ((def, {parent, oper}), acc) =
                    case ParentMap.find acc parent
                    of SOME vs => ParentMap.insert acc (parent, DefSet.add (vs, def))
                     | NONE => ParentMap.insert acc (parent, DefSet.singleton def)
            in Map.fold step ParentMap.empty stmts
            end

        fun exprsToDoc ({stmts, ...}: t) visited exprs =
            let fun depsToDoc oper =
                    Expr.foldDeps (fn (depDef, acc) => acc <++> stmtToDoc depDef)
                                  PPrint.empty oper

                and stmtToDoc def =
                    if not (DefSet.member (exprs, def))
                       orelse DefSetMut.member (visited, def)
                    then PPrint.empty
                    else let do DefSetMut.add (visited, def)
                             val {parent = _, oper} = Map.lookup stmts def
                         in depsToDoc oper
                            <++> CpsId.toDoc def <+> text "=" <+> Expr.operToDoc oper
                         end
            in DefSet.foldl (fn (def, acc) => acc <++> stmtToDoc def) PPrint.empty exprs
            end

        fun fnToDoc (program as {stmts, conts, ...} : t) visited label exprs =
            let val {name, tParams, vParams, body} = LabelMap.lookup conts label
            in Label.toDoc label <+> text "=" <+> text "fn"
               <> Option.mapOr (fn name => space <> Name.toDoc name) PPrint.empty name
               <+> brackets (punctuate (comma <> space) (Vector.map FType.defToDoc tParams))
               <+> parens (punctuate (comma <> space) (Vector.map Type.toDoc vParams))
               <> nest 4 (newline <> exprsToDoc program visited exprs <++> Cont.Transfer.toDoc body)
            end

        fun stmtsToDoc (program as {conts, ...} : t) =
            let val visited = DefSetMut.mkEmpty 0
                val grouped = byParent program
            in LabelMap.fold (fn ((label, _), acc) =>
                                  let val exprs = getOpt (ParentMap.find grouped (SOME label), DefSet.empty)
                                  in acc <++> newline <> fnToDoc program visited label exprs
                                  end)
                             (case ParentMap.find grouped NONE
                              of SOME exprs => exprsToDoc program visited exprs
                               | NONE => PPrint.empty)
                             conts
            end

        fun typeFnToDoc def = text "type" <+> FType.defToDoc def

        (* MAYBE: Nest functions in output: *)
        fun toDoc (program as {typeFns, stmts = _, conts, main}) =
            punctuate newline (Vector.map typeFnToDoc typeFns)
            <++> newline <> newline <> stmtsToDoc program
            <++> newline <> newline <> text "entry" <+> Label.toDoc main

        (* OPTIMIZE: Transient Map: *)
        structure Builder = struct
            type builder = {typeFns : FType.def vector, stmts : Expr.t Map.t ref, conts : Cont.t LabelMap.t ref}

            fun new typeFns = {typeFns, stmts = ref Map.empty, conts = ref LabelMap.empty}

            fun insertCont ({conts, ...} : builder) kv = conts := LabelMap.insert (!conts) kv

            fun insert {typeFns = _, stmts, conts = _} stmt = stmts := Map.insert (!stmts) stmt

            fun express builder expr =
                let val def = CpsId.fresh ()
                    do insert builder (def, expr)
                in def
                end

            fun build {typeFns, stmts, conts} main = {typeFns, stmts = !stmts, conts = !conts, main}
        end
    end
end

