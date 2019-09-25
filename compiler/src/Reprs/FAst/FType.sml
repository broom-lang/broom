signature FAST_TYPE = sig
    structure Id: ID
    structure Prim: PRIM_TYPE where type t = PrimType.t

    datatype effect = Pure | Impure

    type arrow = effect Cst.explicitness

    datatype kind = ArrowK of Pos.t * {domain: kind, codomain: kind}
                  | TypeK of Pos.t
                  | RowK of Pos.t
                  | CallsiteK of Pos.t

    type def = {var: Id.t, kind: kind}

    type tfn_sig = {paramKinds: kind vector, kind: kind}

    datatype 'sv concr
        = ForAll of Pos.t * def vector * 'sv concr
        | Arrow of Pos.t * arrow * {domain: 'sv concr, codomain: 'sv concr}
        | Record of Pos.t * 'sv concr
        | RowExt of Pos.t * {field: Name.t * 'sv concr, ext: 'sv concr}
        | EmptyRow of Pos.t
        | Type of Pos.t * 'sv abs
        | App of Pos.t * {callee: 'sv concr, arg: 'sv concr}
        | CallTFn of Pos.t * Name.t * 'sv concr vector
        | UseT of Pos.t * def
        | SVar of Pos.t * 'sv
        | Prim of Pos.t * Prim.t
    
    and 'sv abs
        = Exists of Pos.t * def vector * 'sv concr

    and 'sv co
        = Refl of 'sv concr
        | Symm of 'sv co
        | UseCo of Name.t (* HACK *)

    val kindToDoc: kind -> PPrint.t
    val kindToString: kind -> string
    val defToDoc: def -> PPrint.t
    val arrowDoc: arrow -> PPrint.t
    val piEffect: 'sv concr -> effect option
    val rowExtTail: 'sv concr -> 'sv concr
    val unit: Pos.t -> 'sv concr
    
    structure Concr: sig
        val pos: 'sv concr -> Pos.t
        val toDoc: ('sv -> PPrint.t) -> 'sv concr -> PPrint.t
        val toString: ('sv -> PPrint.t) -> 'sv concr -> string
        val isSmall: 'sv concr -> bool
        val occurs: ('uv -> 'sv -> bool) -> 'uv -> 'sv concr -> bool
        val substitute: ('sv concr Id.SortedMap.map -> 'sv -> 'sv concr option)
                        -> 'sv concr Id.SortedMap.map -> 'sv concr -> 'sv concr
        val kindOf: (Pos.t * 'sv -> kind) -> (Name.t -> tfn_sig) -> 'sv concr -> kind
    end

    structure Abs: sig
        val pos: 'sv abs -> Pos.t
        val toDoc: ('sv -> PPrint.t) -> 'sv abs -> PPrint.t
        val toString: ('sv -> PPrint.t) -> 'sv abs -> string
        val occurs: ('uv -> 'sv -> bool) -> 'uv -> 'sv abs -> bool
        val concr: 'sv concr -> 'sv abs
        val substitute: ('sv concr Id.SortedMap.map -> 'sv -> 'sv concr option)
                        -> 'sv concr Id.SortedMap.map -> 'sv abs -> 'sv abs
        val kindOf: (Pos.t * 'sv -> kind) -> (Name.t -> tfn_sig) -> 'sv abs -> kind
    end

    structure Co: sig
        val toDoc: ('sv -> PPrint.t) -> 'sv co -> PPrint.t
    end
end

structure FType :> FAST_TYPE = struct
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<|> = PPrint.<|>
    val comma = PPrint.comma
    val space = PPrint.space
    val newline = PPrint.newline
    val parens = PPrint.parens
    val brackets = PPrint.brackets
    val braces = PPrint.braces
    val align = PPrint.align

    structure Id = Id(struct end)

    structure Prim = PrimType

    datatype effect = Pure | Impure

    type arrow = effect Cst.explicitness

    datatype kind = ArrowK of Pos.t * {domain: kind, codomain: kind}
                  | TypeK of Pos.t
                  | RowK of Pos.t
                  | CallsiteK of Pos.t

    type def = {var: Id.t, kind: kind}

    type tfn_sig = {paramKinds: kind vector, kind: kind}

    datatype 'sv concr
        = ForAll of Pos.t * def vector * 'sv concr
        | Arrow of Pos.t * arrow * {domain: 'sv concr, codomain: 'sv concr}
        | Record of Pos.t * 'sv concr
        | RowExt of Pos.t * {field: Name.t * 'sv concr, ext: 'sv concr}
        | EmptyRow of Pos.t
        | Type of Pos.t * 'sv abs
        | App of Pos.t * {callee: 'sv concr, arg: 'sv concr}
        | CallTFn of Pos.t * Name.t * 'sv concr vector
        | UseT of Pos.t * def
        | SVar of Pos.t * 'sv
        | Prim of Pos.t * Prim.t
    
    and 'sv abs
        = Exists of Pos.t * def vector * 'sv concr

    and 'sv co
        = Refl of 'sv concr
        | Symm of 'sv co
        | UseCo of Name.t

    val arrowDoc =
        fn Cst.Implicit => text "=>"
         | Cst.Explicit Pure => text "->"
         | Cst.Explicit Impure => text "~>"

    val rec kindToDoc =
        fn TypeK _ => text "Type"
         | RowK _ => text "Row"
         | ArrowK (_, {domain, codomain}) =>
            kindToDoc domain <+> text "->" <+> kindToDoc codomain
         | CallsiteK _ => text "Callsite"

    val kindToString = PPrint.pretty 80 o kindToDoc

    fun idToDoc id = text ("g__" ^ Id.toString id)

    fun defToDoc {var, kind} = idToDoc var <> text ":" <+> kindToDoc kind

    fun concrToDoc svarToDoc =
        let val rec concrToDoc =
                fn ForAll (_, params, t) =>
                    text "forall" <+> PPrint.punctuate space (Vector.map defToDoc params)
                        <+> text "." <+> concrToDoc t
                 | Arrow (_, arrow, {domain, codomain}) =>
                    concrToDoc domain <+> arrowDoc arrow <+> concrToDoc codomain
                 | Record (_, row) =>
                    let val oneLiner = braces (rowToOneLiner svarToDoc row)
                        val multiLiner =
                            align (braces (space <> rowToMultiLiner svarToDoc row<> space))
                    in oneLiner <|> multiLiner
                    end
                 | row as RowExt _ =>
                    let val oneLiner = text "(|" <> rowToOneLiner svarToDoc row <> text "|)"
                        val multiLiner =
                            text "(|"
                                <> align (braces (space <> rowToMultiLiner svarToDoc row <> space))
                                <> text "|)"
                    in oneLiner <|> multiLiner
                    end
                 | EmptyRow _ => text "(||)"
                 | Type (_, t) => brackets (text "=" <+> absToDoc svarToDoc t)
                 | App (_, {callee, arg}) => concrToDoc callee <+> concrToDoc arg
                 | CallTFn (_, f, args) =>
                    Name.toDoc f <> parens (PPrint.punctuate (comma <> space) (Vector.map concrToDoc args))
                 | SVar (_, sv) => svarToDoc sv
                 | UseT (_, {var, kind = _}) => idToDoc var
                 | Prim (_, p) => Prim.toDoc p
        in concrToDoc
        end

    and rowToOneLiner svarToDoc =
        fn RowExt (_, {field, ext}) =>
            fieldToDoc svarToDoc field
                <> (case ext
                    of RowExt _ => text "," <+> rowToOneLiner svarToDoc ext
                     | EmptyRow _ => PPrint.empty
                     | _ => space <> text "|" <+> concrToDoc svarToDoc ext)
         | EmptyRow _ => PPrint.empty
         | t => concrToDoc svarToDoc t

    and rowToMultiLiner svarToDoc =
        fn RowExt (_, {field, ext}) =>
            fieldToDoc svarToDoc field
                <> (case ext
                    of RowExt _ => newline <> text "," <+> rowToMultiLiner svarToDoc ext
                     | EmptyRow _ => PPrint.empty
                     | _ => newline <> text "|" <+> concrToDoc svarToDoc ext)
         | EmptyRow _ => PPrint.empty
         | t => concrToDoc svarToDoc t

    and fieldToDoc svarToDoc (label, fieldt) =
        Name.toDoc label <> text ":" <+> concrToDoc svarToDoc fieldt

    and absToDoc svarToDoc =
        fn Exists (_, #[], t) => concrToDoc svarToDoc t
         | Exists (_, params, t) =>
            text "exists" <+> PPrint.punctuate space (Vector.map defToDoc params)
                <+> text "." <+> concrToDoc svarToDoc t

    and coercionToDoc svarToDoc =
        fn Refl t => concrToDoc svarToDoc t
         | Symm co => text "symm" <+> coercionToDoc svarToDoc co
         | UseCo name => Name.toDoc name

    fun mapConcrChildren f =
        fn ForAll (pos, param, body) => ForAll (pos, param, f body)
         | Arrow (pos, arrow, {domain, codomain}) =>
            Arrow (pos, arrow, {domain = f domain, codomain = f codomain})
         | Record (pos, row) => Record (pos, f row)
         | RowExt (pos, {field = (label, fieldt), ext}) =>
            RowExt (pos, {field = (label, f fieldt), ext = f ext})
         | App (pos, {callee, arg}) => App (pos, {callee = f callee, arg = f arg})
         | CallTFn (pos, name, args) => CallTFn (pos, name, Vector.map f args)
         | t as (EmptyRow _ | Type _ | SVar _ | UseT _ | Prim _) => t

    fun mapAbsChildren f =
        fn Exists (pos, params, t) => Exists (pos, params, f t)

    fun concrCata (alg as {forAll, arrow, record, rowExt, emptyRow, typ, svar, app, callTFn, uset, prim}) =
        fn ForAll (pos, param, body) => forAll (pos, param, concrCata alg body)
         | Arrow (pos, arr, {domain, codomain}) =>
            arrow (pos, arr, {domain = concrCata alg domain, codomain = concrCata alg codomain})
         | Record (pos, row) => record (pos, concrCata alg row)
         | RowExt (pos, {field = (label, fieldt), ext}) =>
            rowExt (pos, {field = (label, concrCata alg fieldt), ext = concrCata alg ext})
         | EmptyRow args => emptyRow args
         | Type args => typ args
         | SVar args => svar args
         | App (pos, {callee, arg}) =>
            app (pos, {callee = concrCata alg callee, arg = concrCata alg arg})
         | CallTFn (pos, name, args) => callTFn (pos, name, Vector.map (concrCata alg) args)
         | UseT args => uset args
         | Prim args => prim args

    fun absCata {exists, concr} =
        fn Exists (pos, params, body) => exists (pos, params, concr body)

    fun concrOccurs svarOcc sv = concrCata { forAll = #3
                                           , arrow = fn (_, _, {domain, codomain}) => domain orelse codomain
                                           , record = #2
                                           , rowExt = fn (_, {field = (_, fieldt), ext}) => fieldt orelse ext
                                           , emptyRow = Fn.constantly false
                                           , typ = fn (_, t) => absOccurs svarOcc sv t
                                           , svar = fn (_, sv') => svarOcc sv sv'
                                           , app = fn (_, {callee, arg}) => callee orelse arg
                                           , callTFn = fn (_, _, args) => Vector.exists Fn.identity args
                                           , uset = Fn.constantly false
                                           , prim = Fn.constantly false }

    and absOccurs svarOcc sv = absCata { exists = #3
                                       , concr = concrOccurs svarOcc sv }

    (* OPTIMIZE: Entire subtrees where the `name` does not occur could be reused. *)
    fun concrSubstitute svarSubst mapping =
        let fun subst mapping =
                fn t as ForAll (_, params, _) =>
                    let val mapping = Vector.foldl (fn ({var, ...}, mapping) =>
                                                        (#1 (Id.SortedMap.remove (mapping, var)))
                                                        handle _ => mapping)
                                                   mapping params
                    in mapConcrChildren (subst mapping) t
                    end
                 | t as (Arrow _ | Record _ | RowExt _ | EmptyRow _ | App _ | CallTFn _ | Prim _) =>
                    mapConcrChildren (subst mapping) t
                 | Type (pos, t) => Type (pos, absSubstitute svarSubst mapping t)
                 | t as UseT (_, {var, ...}) => getOpt (Id.SortedMap.find (mapping, var), t)
                 | t as SVar (_, sv) => getOpt (svarSubst mapping sv, t)
        in subst mapping
        end

    and absSubstitute svarSubst mapping =
        fn t as Exists (_, params, _) =>
            let val mapping = Vector.foldl (fn ({var, ...}, mapping) =>
                                                (#1 (Id.SortedMap.remove (mapping, var)))
                                                handle _ => mapping)
                                           mapping params
            in mapAbsChildren (concrSubstitute svarSubst mapping) t
            end

    val rec smallConcr =
        fn ForAll (_, params, body) =>
            Vector.length params = 0 andalso smallConcr body
         | Arrow (_, _, {domain, codomain}) =>
            smallConcr domain andalso smallConcr codomain
         | Record (_, t) => smallConcr t
         | RowExt (_, {field = (_, fieldt), ext}) =>
            smallConcr fieldt andalso smallConcr ext
         | EmptyRow _ => true
         | Type (_, t) => smallAbs t
         | App (_, {callee, arg}) => smallConcr callee andalso smallConcr arg
         | CallTFn (_, _, args) => Vector.all smallConcr args
         | SVar _ | UseT _ | Prim _ => true

    and smallAbs =
        fn Exists (_, params, body) =>
            Vector.length params = 0 andalso smallConcr body

    val rec piEffect =
        fn ForAll (_, _, body) => piEffect body
         | Arrow (_, Cst.Implicit, {domain = _, codomain}) => piEffect codomain
         | Arrow (_, Cst.Explicit eff, _) => SOME eff
         | _ => NONE

    val rec rowExtTail =
        fn RowExt (_, {ext, ...}) => rowExtTail ext
         | t => t

    fun unit pos = Prim (pos, Prim.Unit)

    structure Concr = struct
        val pos =
            fn ForAll (pos, _, _) => pos
             | Arrow (pos, _, _) => pos
             | Record (pos, _) => pos
             | RowExt (pos, _) => pos
             | EmptyRow pos => pos
             | Type (pos, _) => pos
             | App (pos, _) => pos
             | CallTFn (pos, _, _) => pos
             | SVar (pos, _) => pos
             | UseT (pos, _) => pos
             | Prim (pos, _) => pos

        val toDoc = concrToDoc
        fun toString svarToDoc = PPrint.pretty 80 o toDoc svarToDoc
        val occurs = concrOccurs
        val substitute = concrSubstitute
        val isSmall = smallConcr

        fun kindOf svarKind (typeFnKind: Name.t -> tfn_sig) =
            fn t as (ForAll _ | Arrow _ | Record _ | Type _ | Prim _)  => TypeK (pos t)
             | t as (RowExt _ | EmptyRow _) => RowK (pos t)
             | CallTFn (_, callee, #[]) => #kind (typeFnKind callee)
             | UseT (_, {kind, ...}) => kind
             | SVar args => svarKind args
    end

    structure Abs = struct
        val pos =
            fn Exists (pos, _, _) => pos

        val toDoc = absToDoc
        fun toString svarToDoc = PPrint.pretty 80 o toDoc svarToDoc
        val occurs = absOccurs
        val substitute = absSubstitute
        val isSmall = smallAbs

        fun concr t = Exists (Concr.pos t, #[], t)

        fun kindOf svarKind typeFnKind =
            fn Exists (_, _, t) => Concr.kindOf svarKind typeFnKind t
    end

    structure Co = struct
        val toDoc = coercionToDoc
    end
end

signature CLOSED_FAST_TYPE = sig
    structure Id: ID where type t = FType.Id.t
    structure Prim: PRIM_TYPE where type t = PrimType.t
    structure ScopeId: ID

    datatype kind = datatype FType.kind
    type def = FType.def
    type tfn_sig = FType.tfn_sig

    type arrow = FType.arrow

    datatype concr' = datatype FType.concr
    datatype abs' = datatype FType.abs
    datatype co' = datatype FType.co

    type sv
    type concr = sv FType.concr
    type abs = sv FType.abs
    type co = sv FType.co

    val kindToDoc: kind -> PPrint.t
    val defToDoc: def -> PPrint.t
    val arrowDoc: arrow -> PPrint.t
    val svarToDoc: sv -> PPrint.t
    val rowExtTail: concr -> concr
    val unit: Pos.t -> concr

    structure Concr: sig
        val pos: concr -> Pos.t
        val toDoc: concr -> PPrint.t
        val substitute: (ScopeId.t -> bool) ->concr Id.SortedMap.map -> concr -> concr
    end

    structure Abs: sig
        val pos: abs -> Pos.t
        val toDoc: abs -> PPrint.t
        val concr: concr -> abs
    end

    structure Co: sig
        val toDoc: co -> PPrint.t
    end
end

