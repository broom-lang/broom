signature CPS_TYPE = sig
    structure Id : ID
        where type t = FAst.Type.Id.t
        where type 'v SortedMap.map = 'v FAst.Type.Id.SortedMap.map
    structure Prim : PRIM_TYPE where type t = PrimType.t

    type param = FAst.Type.def
    
    datatype t
        = FnT of {tDomain : param vector, vDomain : t vector}
        | AnyClosure of {tDomain : param vector, vDomain : t vector}
        | Closure of {tDomain : param vector, vDomain : t vector, clovers : t vector}
        | AppT of {callee : t, args : t vector1}
        | Record of t
        | Results of t vector
        | EmptyRow
        | Singleton of CpsId.t
        | Type of t
        | TParam of param
        | Prim of Prim.t

    val toDoc : t -> PPrint.t

    val fromF : FAst.Type.concr -> t
    val eq : t * t -> bool
    val substitute : t Id.SortedMap.map -> t -> t
    val mapChildren : (t -> t) -> t -> t

    structure Coercion : sig
        datatype co = Refl of t

        val toDoc : co -> PPrint.t
    end
end

signature CPS_GLOBAL = sig
    structure Type : CPS_TYPE

    datatype t
        = Layout of layout

    withtype layout =
        { size : LargeWord.word option
        , align : Word.word option
        , inlineable : bool
        , isArray : bool
        , fields : {offset : LargeWord.word option, layout : Name.t option} vector }

    val toDoc : t -> PPrint.t
    val blobLayout : int -> t
    val boxLayout : int -> t
    val appDeps : (Name.t -> unit) -> t -> unit
end

signature CPS_EXPR = sig
    structure Type : CPS_TYPE

    type def = CpsId.t

    structure ParentMap : HASH_MAP where type key = Label.t option

    datatype oper
        = PrimApp of {opn : Primop.t, tArgs : Type.t vector, vArgs : def vector}
        | Result of def * int
        | EmptyRecord
        | With of {base : def, field : Name.t * def}
        | Where of {base : def, field : Name.t * def}
        | Without of {base : def, field : Name.t}
        | Field of def * Name.t
        | ClosureNew of def * Label.t * def vector
        | ClosureFn of def
        | Clover of def * int
        | Cast of def * Type.Coercion.co
        | Type of Type.t
        | Global of Name.t
        | Label of Label.t
        | Param of Label.t * int
        | Const of Const.t

    type t = {parent : Label.t option, typ : Type.t, oper : oper}

    val toDoc : t -> PPrint.t

    val typeOf : t -> Type.t
    val primopType : Primop.t
        -> {tParams : Type.param vector, vParams : Type.t vector, codomain : Type.t vector vector}
    val foldDeps : (CpsId.t * 'a -> 'a) -> 'a -> oper -> 'a
    val foldLabels : (Label.t * 'a -> 'a) -> 'a -> oper -> 'a
    val mapDefs : (CpsId.t -> CpsId.t) -> oper -> oper
end

signature CPS_TRANSFER = sig
    structure Type : CPS_TYPE

    type def = CpsId.t

    datatype pat
        = AnyP
        | ConstP of Const.t

    datatype t
        = Goto of {callee : Label.t, tArgs : Type.t vector, vArgs : def vector}
        | Jump of {callee : def, tArgs : Type.t vector, vArgs : def vector}
        | Match of def * {pattern : pat, target : Label.t} vector
        | Checked of { opn : Primop.t , tArgs : Type.t vector, vArgs : def vector
                     , succeed : Label.t, fail : Label.t }
        | Return of Type.t vector * def vector

    val toDoc : t -> PPrint.t

    val foldlDeps : (def * 'a -> 'a) -> 'a -> t -> 'a
    val foldrDeps : (def * 'a -> 'a) -> 'a -> t -> 'a
    val mapDefs : (def -> def) -> t -> t
    val foldLabels : (Label.t * 'a -> 'a) -> 'a -> t -> 'a
end

signature CPS_CONT = sig
    structure Type : CPS_TYPE
    structure Transfer : CPS_TRANSFER

    type t =
        { name : Name.t option
        , cconv : CallingConvention.t option
        , tParams : Type.param vector, vParams : Type.t vector
        , body : Transfer.t }

    val toDoc : t -> PPrint.t
end

signature CPS_PROGRAM = sig
    structure Global : CPS_GLOBAL
    structure Expr : CPS_EXPR
    structure Cont : CPS_CONT

    structure Map : HASH_MAP
        where type key = CpsId.t
        where type 'v t = 'v CpsId.HashMap.t
    structure LabelMap : HASH_MAP
        where type key = Label.t
        where type 'v t = 'v Label.HashMap.t

    (* TODO: Make abstract? *)
    type t =
        { typeFns : Expr.Type.param vector
        , globals : Global.t Name.HashMap.t
        , stmts : Expr.t Map.t
        , conts : Cont.t LabelMap.t
        , main : Label.t }

    val defSite : t -> CpsId.t -> Expr.t
    val defType : t -> CpsId.t -> Expr.Type.t
    val labelCont : t -> Label.t -> Cont.t
    val global : t -> Name.t -> Global.t
    val byParent : t -> CpsId.SortedSet.set Expr.ParentMap.t

    val toDoc : t -> PPrint.t

    structure Builder : sig
        type builder

        val new : Expr.Type.param vector -> builder
        val insertGlobal : builder -> Name.t * Global.t -> unit
        val insertCont : builder -> Label.t * Cont.t -> unit
        val insertExpr : builder -> Expr.def * Expr.t -> unit
        val express : builder -> Expr.t -> Expr.def
        val build : builder -> Label.t -> t
    end
end

structure Cps :> sig
    structure Type : CPS_TYPE
    structure Global : CPS_GLOBAL where type Type.t = Type.t
    structure Expr : CPS_EXPR
        where type Type.t = Type.t
        where type Type.Coercion.co = Type.Coercion.co
    structure Transfer : CPS_TRANSFER where type Type.t = Type.t
    structure Cont : CPS_CONT
        where type Type.t = Type.t
        where type Transfer.t = Transfer.t
    structure Program : CPS_PROGRAM
        where type Global.t = Global.t
        where type Expr.Type.t = Type.t
        where type Expr.oper = Expr.oper
        where type Cont.Type.t = Cont.Type.t
        where type Cont.Transfer.t = Cont.Transfer.t
end = struct
    structure DefSet = CpsId.SortedSet
    structure DefSetMut = CpsId.HashSetMut

    val op|> = Fn.|>
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
        structure Id = FAst.Type.Id
        structure Prim = PrimType

        type param = FAst.Type.def
        
        datatype t
            = FnT of {tDomain : param vector, vDomain : t vector}
            | AnyClosure of {tDomain : param vector, vDomain : t vector}
            | Closure of {tDomain : param vector, vDomain : t vector, clovers : t vector}
            | AppT of {callee : t, args : t vector1}
            | Record of t
            | Results of t vector
            | EmptyRow
            | Singleton of CpsId.t
            | Type of t
            | TParam of param
            | Prim of Prim.t

        fun argsDoc toDoc =
            fn #[] => PPrint.empty
             | ts => brackets (punctuate (comma <> space) (Vector.map toDoc ts))

        val rec toDoc =
            fn FnT {tDomain, vDomain} =>
                text "fn"
                <+> argsDoc FAst.Type.defToDoc tDomain
                <+> parens (punctuate (comma <> space) (Vector.map toDoc vDomain))
             | AnyClosure {tDomain, vDomain} =>
                text "cl"
                <+> argsDoc FAst.Type.defToDoc tDomain
                <+> parens (punctuate (comma <> space) (Vector.map toDoc vDomain))
             | Closure {tDomain, vDomain, clovers} =>
                text "cl"
                <+> argsDoc FAst.Type.defToDoc tDomain
                <+> parens (punctuate (comma <> space) (Vector.map toDoc vDomain))
                <+> braces (punctuate (comma <> space) (Vector.map toDoc clovers))
             | AppT {callee, args} =>
                parens (toDoc callee <+> punctuate space (Vector.map toDoc (Vector1.toVector args)))
             | Record row => braces (toDoc row)
             | Results ts => parens (punctuate (comma <> space) (Vector.map toDoc ts))
             | EmptyRow => PPrint.empty
             | Singleton def => text "val" <+> CpsId.toDoc def
             | Type t => brackets (text "=" <+> toDoc t)
             | TParam {var, ...} => text ("g__" ^ Id.toString var) (* HACK: g__ *)
             | Prim p => Prim.toDoc p

        val rec fromF =
            fn FAst.Type.ForAll (params, body) =>
                let val contTyp = FnT {tDomain = #[], vDomain = #[Prim Prim.StackT, fromF body]}
                in FnT {tDomain = Vector1.toVector params, vDomain = #[Prim Prim.StackT, contTyp]}
                end
             | FAst.Type.Arrow (_, {domain, codomain}) =>
                let val contTyp = FnT {tDomain = #[], vDomain = #[Prim Prim.StackT, fromF codomain]}
                in FnT {tDomain = #[], vDomain = #[Prim Prim.StackT, fromF domain, contTyp]}
                end
             | FAst.Type.Record row => Record (fromF row)
             | FAst.Type.EmptyRow => EmptyRow
             | FAst.Type.Type t => Type (fromF t)
             | FAst.Type.App {callee, args} =>
                AppT {callee = fromF callee, args = Vector1.map fromF args}
             | FAst.Type.UseT def => TParam def
             | FAst.Type.Prim p => Prim p

        val rec eq =
            fn ( (FnT {tDomain, vDomain}, FnT {tDomain = tDomain', vDomain = vDomain'})
               | (AnyClosure {tDomain, vDomain}, AnyClosure {tDomain = tDomain', vDomain = vDomain'}) ) =>
                (case (tDomain, tDomain')
                 of (#[], #[]) =>
                     VectorExt.zip (vDomain, vDomain')
                     |> Vector.all eq
                  | _ => raise Fail "unimplemented")
             | (Closure {tDomain, vDomain, clovers}, Closure {tDomain = tDomain', vDomain = vDomain', clovers = clovers'}) =>
                (case (tDomain, tDomain')
                 of (#[], #[]) =>
                     ( VectorExt.zip (vDomain, vDomain')
                     |> Vector.all eq )
                     andalso VectorExt.zip (clovers, clovers') |> Vector.all eq
                  | _ => raise Fail "unimplemented")
             | (AppT {callee, args}, AppT {callee = callee', args = args'}) =>
                eq (callee, callee')
                andalso Vector1.length args = Vector1.length args'
                andalso Vector1.all eq (Vector1.zip (args, args'))
             | (Record row, Record row') => eq (row, row')
             | (EmptyRow, EmptyRow) => true
             | (Results ts, Results ts') => VectorExt.zip (ts, ts') |> Vector.all eq
             | (Singleton def, Singleton def') => CpsId.eq (def, def')
             | (Prim p, Prim p') => true
             | (t, t') =>
                raise Fail ("unimplemented " ^ PPrint.pretty 80 (toDoc t <+> text "?=" <+> toDoc t'))

        fun mapChildren f t =
            case t
            of FnT {tDomain, vDomain} => FnT {tDomain, vDomain = Vector.map f vDomain}
             | Closure {tDomain, vDomain, clovers} =>
                Closure {tDomain, vDomain = Vector.map f vDomain, clovers = Vector.map f clovers}
             | AnyClosure {tDomain, vDomain} =>
                AnyClosure {tDomain, vDomain = Vector.map f vDomain}
             | AppT {callee, args} => AppT {callee = f callee, args = Vector1.map f args}
             | Record row => Record (f row)
             | Results ts => Results (Vector.map f ts)
             | Type t => Type (f t)
             | (TParam _ | EmptyRow | Singleton _ | Prim _) => t

        fun substitute mapping =
            fn t as FnT {tDomain, vDomain} =>
                let val mapping =
                        Vector.foldl (fn ({var, ...}, mapping) =>
                                          #1 (Id.SortedMap.remove (mapping, var)))
                                     mapping tDomain
                in mapChildren (substitute mapping) t
                end
             | t as TParam {var, ...} =>
                (case Id.SortedMap.find (mapping, var)
                 of SOME t' => t'
                  | NONE => t)
             | t => mapChildren (substitute mapping) t

        structure Coercion = struct
            datatype co = Refl of t

            val toDoc =
                fn Refl t => toDoc t
        end
    end

    structure Global = struct
        structure Type = Type

        datatype t
            = Layout of layout

        withtype layout =
            { size : LargeWord.word option
            , align : Word.word option
            , inlineable : bool
            , isArray : bool
            , fields : {offset : LargeWord.word option, layout : Name.t option} vector }

        fun fieldLayoutToDoc {offset, layout} =
            braces ( text "offset" <+> text "="
                   <+> (case offset
                        of SOME offset => PPrint.largeWord offset
                         | NONE => text "?") <> comma
                   <+> text "layout" <+> text "="
                   <+> (case layout
                        of SOME layout => Name.toDoc layout
                         | NONE => text "?") )

        fun layoutToDoc {size, align, inlineable, isArray, fields} =
            text "Layout"
            <+> braces (nest 4 ( newline
                               <> text "size" <+> text "="
                               <+> (case size
                                    of SOME size => PPrint.largeWord size
                                     | NONE => text "?") <> comma
                               <++> text "align" <+> text "="
                               <+> (case align
                                    of SOME align => PPrint.word align
                                     | NONE => text "?") <> comma
                               <++> text "inlineable" <+> text "=" <+> PPrint.bool inlineable <> comma
                               <++> text "isArray" <+> text "=" <+> PPrint.bool isArray <> comma
                               <++> text "fields" <+> text "="
                               <+> brackets (nest 4 (newline <> punctuate (comma <> newline)
                                                                          (Vector.map fieldLayoutToDoc fields))) )
                       <> newline)

        val toDoc =
            fn Layout layout => layoutToDoc layout

        fun blobLayout size =
            let val size = LargeWord.fromInt size
            in Layout { size = SOME size
                      , align = SOME (Word.fromLargeWord size)
                      , inlineable = true
                      , isArray = false
                      , fields = #[] }
            end

        fun boxLayout size =
            let val size = LargeWord.fromInt size
            in Layout { size = SOME size
                      , align = SOME (Word.fromLargeWord size)
                      , inlineable = false
                      , isArray = false
                      , fields = #[{ offset = SOME 0w0
                                   , layout = SOME (Name.fromString "layout_ORef") }] }
            end

        fun appFieldLayoutDeps f {offset, layout} = Option.app f layout

        fun appDeps f =
            fn Layout {fields, ...} => Vector.app (appFieldLayoutDeps f) fields
    end

    structure Transfer = struct
        structure Type = Type

        type def = CpsId.t

        datatype pat
            = AnyP
            | ConstP of Const.t

        datatype t
            = Goto of {callee : Label.t, tArgs : Type.t vector, vArgs : def vector}
            | Jump of {callee : def, tArgs : Type.t vector, vArgs : def vector}
            | Match of def * {pattern : pat, target : Label.t} vector
            | Checked of { opn : Primop.t , tArgs : Type.t vector, vArgs : def vector
                         , succeed : Label.t, fail : Label.t }
            | Return of Type.t vector * def vector

        val patToDoc =
            fn AnyP => text "_"
             | ConstP c => Const.toDoc c

        fun clauseToDoc {pattern, target} =
            patToDoc pattern <+> text "->" <+> Label.toDoc target

        val toDoc =
            fn Goto {callee, tArgs, vArgs} =>
                text "goto" <+> Label.toDoc callee
                <+> Type.argsDoc Type.toDoc tArgs
                <+> parens (punctuate (comma <> space) (Vector.map CpsId.toDoc vArgs))
             | Jump {callee, tArgs, vArgs} =>
                text "jump" <+> CpsId.toDoc callee
                <+> Type.argsDoc Type.toDoc tArgs
                <+> parens (punctuate (comma <> space) (Vector.map CpsId.toDoc vArgs))
             | Match (matchee, clauses) =>
                text "match" <+> CpsId.toDoc matchee
                <> nest 4 (newline <> punctuate newline (Vector.map clauseToDoc clauses))
             | Checked {opn, tArgs, vArgs, succeed, fail} =>
                text "checked" <+> Primop.toDoc opn
                <+> Type.argsDoc Type.toDoc tArgs
                <+> parens (punctuate (comma <> space) (Vector.map CpsId.toDoc vArgs))
                <> nest 4 (newline <> text "_" <+> text "->" <+> Label.toDoc succeed
                           <++> text "->" <+> Label.toDoc fail)
             | Return (domain, args) =>
                text "return"
                <+> Type.argsDoc Type.toDoc domain 
                <+> parens (punctuate (comma <> space) (Vector.map CpsId.toDoc args))

        fun foldlDeps f acc =
            fn Goto {callee = _, tArgs = _, vArgs} => Vector.foldl f acc vArgs
             | Jump {callee, tArgs = _, vArgs} => Vector.foldl f (f (callee, acc)) vArgs
             | Match (matchee, _) => f (matchee, acc)
             | Checked {opn = _, tArgs = _, vArgs, succeed = _, fail = _} => Vector.foldl f acc vArgs
             | Return (_, args) => Vector.foldl f acc args

        fun foldrDeps f acc =
            fn Goto {callee = _, tArgs = _, vArgs} => Vector.foldr f acc vArgs
             | Jump {callee, tArgs = _, vArgs} => f (callee, Vector.foldr f acc vArgs)
             | Match (matchee, _) => f (matchee, acc)
             | Checked {opn = _, tArgs = _, vArgs, succeed = _, fail = _} => Vector.foldr f acc vArgs
             | Return (_, args) => Vector.foldr f acc args

        fun mapDefs f =
            fn Goto {callee, tArgs, vArgs} =>
                Goto {callee, tArgs, vArgs = Vector.map f vArgs}
             | Jump {callee, tArgs, vArgs} =>
               Jump {callee = f callee, tArgs, vArgs = Vector.map f vArgs}
             | Match (matchee, clauses) => Match (f matchee, clauses)
             | Checked {opn, tArgs, vArgs, succeed, fail} =>
                Checked {opn, tArgs, vArgs = Vector.map f vArgs, succeed, fail}
             | Return (domain, args) => Return (domain, Vector.map f args)

        fun foldLabels f acc =
            fn Goto {callee, ...} => f (callee, acc)
             | Jump _ => acc
             | Match (_, clauses) =>
                Vector.foldl (fn ({pattern = _, target}, acc) => f (target, acc))
                             acc clauses
             | Checked {opn = _, tArgs = _, vArgs = _, succeed, fail} => f (fail, f (succeed, acc))
             | Return _ => acc
    end

    structure Cont = struct
        structure Type = Type
        structure Transfer = Transfer

        type t =
            { name : Name.t option
            , cconv : CallingConvention.t option
            , tParams : Type.param vector, vParams : Type.t vector
            , body : Transfer.t }

        fun toDoc {name, cconv, tParams, vParams, body} =
            text "fn"
            <> (case cconv
                of SOME cconv => space <> CallingConvention.toDoc cconv
                 | NONE => PPrint.empty)
            <> (case name
                of SOME name => space <> Name.toDoc name
                 | NONE => PPrint.empty)
            <+> Type.argsDoc FAst.Type.defToDoc tParams
            <+> parens (punctuate (comma <> space) (Vector.map Type.toDoc vParams))
            <> nest 4 (newline <> Transfer.toDoc body)
    end

    structure Expr = struct
        structure Type = Type

        type def = CpsId.t

        structure ParentMap = HashMapFn(struct
            type hash_key = Label.t option

            val hashVal = Option.hash Label.hash
            val sameKey = op=
            val toString =
                fn SOME def => Label.toString def
                 | NONE => "-"
        end)

        datatype oper
            = PrimApp of {opn : Primop.t, tArgs : Type.t vector, vArgs : def vector}
            | Result of def * int
            | EmptyRecord
            | With of {base : def, field : Name.t * def}
            | Where of {base : def, field : Name.t * def}
            | Without of {base : def, field : Name.t}
            | Field of def * Name.t
            | ClosureNew of def * Label.t * def vector
            | ClosureFn of def
            | Clover of def * int
            | Cast of def * Type.Coercion.co
            | Type of Type.t
            | Global of Name.t
            | Label of Label.t
            | Param of Label.t * int
            | Const of Const.t

        type t = {parent : Label.t option, typ : Type.t, oper : oper}

        val typeOf : t -> Type.t = #typ

        fun foldDeps f acc =
            fn PrimApp {opn = _, tArgs = _, vArgs} => Vector.foldl f acc vArgs
             | Result (expr, _) => f (expr, acc)
             | With {base, field = (_, fielde)} => f (fielde, f (base, acc))
             | Where {base, field = (_, fielde)} => f (fielde, f (base, acc))
             | Without {base, field = _} => f (base, acc)
             | Field (expr, _) => f (expr, acc)
             | ClosureNew (layout, _, clovers) => Vector.foldl f (f (layout, acc)) clovers
             | ClosureFn expr => f (expr, acc)
             | Clover (expr, _) => f (expr, acc)
             | Cast (expr, _) => f (expr, acc)
             | EmptyRecord => acc
             | Type _ => acc
             | Global _ => acc
             | Label _ => acc
             | Param _ => acc
             | Const _ => acc

        fun mapDefs f =
            fn PrimApp {opn, tArgs, vArgs} => PrimApp {opn, tArgs, vArgs = Vector.map f vArgs}
             | Result (expr, i) => Result (f expr, i)
             | ClosureNew (layout, label, clovers) => ClosureNew (f layout, label, Vector.map f clovers)
             | ClosureFn expr => ClosureFn (f expr)
             | Clover (expr, i) => Clover (f expr, i)
             | t as (EmptyRecord | Type _ | Global _ | Label _ | Param _ | Const _) => t

        fun foldLabels f acc =
            fn (ClosureNew (_, label, _) | Label label | Param (label, _)) => f (label, acc)
             | (PrimApp _ | Result _ | ClosureFn _ | Clover _ | EmptyRecord | Type _ | Global _ | Const _) => acc

        val operToDoc =
            fn PrimApp {opn, tArgs, vArgs} =>
                Primop.toDoc opn
                <+> Type.argsDoc Type.toDoc tArgs
                <+> parens (punctuate (comma <> space) (Vector.map CpsId.toDoc vArgs))
             | Result (expr, i) => text "result" <+> CpsId.toDoc expr <+> PPrint.int i
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
             | ClosureNew (layout, label, clovers) =>
                text "cl" <+> CpsId.toDoc layout <+> Label.toDoc label
                <+> braces (punctuate (comma <> space) (Vector.map CpsId.toDoc clovers))
             | ClosureFn def => text "code" <+> CpsId.toDoc def
             | Clover (cl, i) => text "clover" <+> CpsId.toDoc cl <+> PPrint.int i
             | Cast (expr, co) => CpsId.toDoc expr <+> text "as" <+> Type.Coercion.toDoc co
             | Type t => brackets (Type.toDoc t)
             | Global name => text "global" <+> Name.toDoc name
             | Label label => text "fn" <+> Label.toDoc label
             | Param (label, i) => text "param" <+> Label.toDoc label <+> PPrint.int i
             | Const c => text "const" <+> Const.toDoc c

        fun toDoc {parent = _, typ, oper} = operToDoc oper <+> text ":" <+> Type.toDoc typ

        (* OPTIMIZE: *)
        fun primopType opn =
            let val (tParams, _, {domain, codomain = (successTyp, hasFailure)}) = FAst.Type.primopType opn
            in  if hasFailure
                then { tParams, vParams = Vector.map Type.fromF domain
                     , codomain = #[#[Type.fromF successTyp], #[]] }
                else if Primop.isTotal opn
                     then { tParams, vParams = Vector.map Type.fromF domain
                          , codomain = #[#[Type.fromF successTyp]] }
                     else { tParams, vParams = VectorExt.prepend (Type.Prim Type.Prim.StackT, Vector.map Type.fromF domain)
                          , codomain = #[#[Type.Prim Type.Prim.StackT, Type.fromF successTyp]] }
            end
    end

    structure Program = struct
        structure Global = Global
        structure Expr = Expr
        structure Map = CpsId.HashMap
        structure LabelMap = Label.HashMap
        structure ParentMap = Expr.ParentMap
        structure Cont = Cont

        type t =
            { typeFns : Type.param vector
            , globals : Global.t Name.HashMap.t
            , stmts : Expr.t Map.t
            , conts : Cont.t LabelMap.t
            , main : Label.t }

        fun defSite ({stmts, ...} : t) def = Map.lookup stmts def

        fun defType program = Expr.typeOf o defSite program

        fun labelCont ({conts, ...} : t) label = LabelMap.lookup conts label

        fun global ({globals, ...} : t) name = Name.HashMap.lookup globals name

        fun byParent ({stmts, ...}: t) =
            let fun step ((def, {parent, typ = _, oper = _}), acc) =
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
                             val expr as {oper, ...} = Map.lookup stmts def
                         in depsToDoc oper
                            <++> CpsId.toDoc def <+> text "=" <+> Expr.toDoc expr
                         end
            in DefSet.foldl (fn (def, acc) => acc <++> stmtToDoc def) PPrint.empty exprs
            end

        fun fnToDoc (program as {stmts, conts, ...} : t) visited label exprs =
            let val {name, cconv, tParams, vParams, body} = LabelMap.lookup conts label
            in text "fun"
               <> (case cconv
                   of SOME cconv => space <> CallingConvention.toDoc cconv <> space
                    | NONE => space)
               <> Label.toDoc label
               <+> Type.argsDoc FAst.Type.defToDoc tParams
               <+> parens (punctuate (comma <> space) (Vector.map Type.toDoc vParams)) <> text ":"
               <> nest 4 (newline <> exprsToDoc program visited exprs <++> Transfer.toDoc body)
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

        fun typeFnToDoc def = text "type" <+> FAst.Type.defToDoc def

        (* MAYBE: Nest functions in output: *)
        fun toDoc (program as {typeFns, globals, stmts = _, conts, main}) =
            punctuate newline (Vector.map typeFnToDoc typeFns)
            <++> newline <> newline
            <> punctuate (newline <> newline)
                         (Vector.map (fn (name, global) =>
                                         text "static" <+> Name.toDoc name <+> text "="
                                         <+> Global.toDoc global)
                                     (Name.HashMap.toVector globals))
            <++> newline <> newline <> stmtsToDoc program
            <++> newline <> newline <> text "entry" <+> Label.toDoc main

        (* OPTIMIZE: Transient Map: *)
        structure Builder = struct
            type builder = { typeFns : Type.param vector, globals : Global.t Name.HashMap.t ref
                           , stmts : Expr.t Map.t ref, conts : Cont.t LabelMap.t ref}

            fun new typeFns =
                { typeFns, globals = ref Name.HashMap.empty
                , stmts = ref Map.empty, conts = ref LabelMap.empty}

            fun insertGlobal ({globals, ...} : builder) kv =
                globals := Name.HashMap.insert (!globals) kv

            fun insertCont ({conts, ...} : builder) kv = conts := LabelMap.insert (!conts) kv

            fun insertExpr ({stmts, ...} : builder) stmt = stmts := Map.insert (!stmts) stmt

            fun express builder expr =
                let val def = CpsId.fresh ()
                    do insertExpr builder (def, expr)
                in def
                end

            fun build {typeFns, globals, stmts, conts} main =
                {typeFns, globals = !globals, stmts = !stmts, conts = !conts, main}
        end
    end
end

