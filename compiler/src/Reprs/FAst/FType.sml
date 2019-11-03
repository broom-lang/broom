signature FAST_TYPE = sig
    structure Id: ID
    structure Prim: PRIM_TYPE where type t = PrimType.t

    datatype effect = Pure | Impure

    type arrow = effect Cst.explicitness

    datatype kind = ArrowK of {domain: kind, codomain: kind}
                  | TypeK
                  | RowK
                  | CallsiteK

    type def = {var: Id.t, kind: kind}

    type tfn_sig = {paramKinds: kind vector, kind: kind}

    datatype 'sv concr
        = Exists of def vector * 'sv concr
        | ForAll of def vector * 'sv concr
        | Arrow of arrow * {domain: 'sv concr, codomain: 'sv concr}
        | Record of 'sv concr
        | RowExt of 'sv row
        | EmptyRow
        | Type of 'sv concr
        | App of {callee: 'sv concr, args: 'sv concr vector}
        | CallTFn of Name.t * 'sv concr vector
        | UseT of def
        | SVar of 'sv
        | Prim of Prim.t

    and 'sv co
        = Refl of 'sv concr
        | Symm of 'sv co
        | AppCo of {callee: 'sv co, args: 'sv concr vector}
        | UseCo of Name.t (* HACK *)

    withtype 'sv row = {base: 'sv concr, field: Name.t * 'sv concr}

    val kindToDoc: kind -> PPrint.t
    val kindToString: kind -> string
    val defToDoc: def -> PPrint.t
    val arrowDoc: arrow -> PPrint.t
    val piEffect: 'sv concr -> effect option
    val rowExtBase: 'sv concr -> 'sv concr
    val app : {callee: 'sv concr, args: 'sv concr vector} -> 'sv concr
    
    structure Concr: sig
        val toDoc: ('sv -> PPrint.t) -> 'sv concr -> PPrint.t
        val toString: ('sv -> PPrint.t) -> 'sv concr -> string
        val mapChildren : ('sv concr -> 'sv concr) -> 'sv concr -> 'sv concr
        val isSmall: 'sv concr -> bool
        val rewriteRow : Name.t -> 'sv concr -> 'sv row option
        val occurs: ('uv -> 'sv -> bool) -> 'uv -> 'sv concr -> bool
        val substitute: ('sv concr Id.SortedMap.map -> 'sv -> 'sv concr option)
                        -> 'sv concr Id.SortedMap.map -> 'sv concr -> 'sv concr
        val kindOf: ('sv -> kind) -> (Name.t -> tfn_sig) -> 'sv concr -> kind
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

    datatype kind = ArrowK of {domain: kind, codomain: kind}
                  | TypeK
                  | RowK
                  | CallsiteK

    type def = {var: Id.t, kind: kind}

    type tfn_sig = {paramKinds: kind vector, kind: kind}

    datatype 'sv concr
        = Exists of def vector * 'sv concr
        | ForAll of def vector * 'sv concr
        | Arrow of arrow * {domain: 'sv concr, codomain: 'sv concr}
        | Record of 'sv concr
        | RowExt of 'sv row
        | EmptyRow
        | Type of 'sv concr
        | App of {callee: 'sv concr, args: 'sv concr vector}
        | CallTFn of Name.t * 'sv concr vector
        | UseT of def
        | SVar of 'sv
        | Prim of Prim.t
    
    and 'sv co
        = Refl of 'sv concr
        | Symm of 'sv co
        | AppCo of {callee: 'sv co, args: 'sv concr vector}
        | UseCo of Name.t

    withtype 'sv row = {base: 'sv concr, field: Name.t * 'sv concr}

    val arrowDoc =
        fn Cst.Implicit => text "=>"
         | Cst.Explicit Pure => text "->"
         | Cst.Explicit Impure => text "~>"

    val rec kindToDoc =
        fn TypeK => text "Type"
         | RowK => text "Row"
         | ArrowK {domain, codomain} =>
            kindToDoc domain <+> text "->" <+> kindToDoc codomain
         | CallsiteK => text "Callsite"

    val kindToString = PPrint.pretty 80 o kindToDoc

    fun idToDoc id = text ("g__" ^ Id.toString id)

    fun defToDoc {var, kind} = idToDoc var <> text ":" <+> kindToDoc kind

    fun concrToDoc svarToDoc =
        let val rec concrToDoc =
                fn Exists (#[], t) => concrToDoc t
                 | Exists (params, t) =>
                    text "exists" <+> PPrint.punctuate space (Vector.map defToDoc params)
                        <+> text "." <+> concrToDoc t
                 | ForAll (params, t) =>
                    text "forall" <+> PPrint.punctuate space (Vector.map defToDoc params)
                        <+> text "." <+> concrToDoc t
                 | Arrow (arrow, {domain, codomain}) =>
                    concrToDoc domain <+> arrowDoc arrow <+> concrToDoc codomain
                 | Record (row) =>
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
                 | EmptyRow => text "(||)"
                 | Type t => brackets (text "=" <+> concrToDoc t)
                 | App {callee, args} =>
                    concrToDoc callee <+> PPrint.punctuate PPrint.space (Vector.map concrToDoc args)
                 | CallTFn (f, args) =>
                    Name.toDoc f <> parens (PPrint.punctuate (comma <> space) (Vector.map concrToDoc args))
                 | SVar sv => svarToDoc sv
                 | UseT {var, kind = _} => idToDoc var
                 | Prim p => Prim.toDoc p
        in concrToDoc
        end

    and rowToOneLiner svarToDoc =
        fn RowExt {base, field} =>
            rowToOneLiner svarToDoc base
                <> (case base
                    of RowExt _ => text "," <+> fieldToDoc svarToDoc field
                     | EmptyRow => fieldToDoc svarToDoc field
                     | _ => space <> text "with" <+> fieldToDoc svarToDoc field)
         | EmptyRow => PPrint.empty
         | t => concrToDoc svarToDoc t

    and rowToMultiLiner svarToDoc =
        fn RowExt {base, field} =>
            rowToMultiLiner svarToDoc base
                <> (case base
                    of RowExt _ => newline <> text "," <+> fieldToDoc svarToDoc field
                     | EmptyRow => fieldToDoc svarToDoc field
                     | _ => newline <> text "with" <+> fieldToDoc svarToDoc field)
         | EmptyRow => PPrint.empty
         | t => concrToDoc svarToDoc t

    and fieldToDoc svarToDoc (label, fieldt) =
        Name.toDoc label <> text ":" <+> concrToDoc svarToDoc fieldt

    and coercionToDoc svarToDoc =
        fn Refl t => concrToDoc svarToDoc t
         | Symm co => text "symm" <+> coercionToDoc svarToDoc co
         | AppCo {callee, args} =>
            coercionToDoc svarToDoc callee
                <+> PPrint.punctuate space (Vector.map (concrToDoc svarToDoc) args)
         | UseCo name => Name.toDoc name

    fun mapConcrChildren f =
        fn Exists (params, body) => Exists (params, f body)
         | ForAll (param, body) => ForAll (param, f body)
         | Arrow (arrow, {domain, codomain}) =>
            Arrow (arrow, {domain = f domain, codomain = f codomain})
         | Record row => Record (f row)
         | RowExt ({base, field = (label, fieldt)}) =>
            RowExt ({base = f base, field = (label, f fieldt)})
         | App {callee, args} => App {callee = f callee, args = Vector.map f args}
         | CallTFn (name, args) => CallTFn (name, Vector.map f args)
         | t as (EmptyRow | Type _ | SVar _ | UseT _ | Prim _) => t

    fun concrCata (alg as {exists, forAll, arrow, record, rowExt, emptyRow, typ, svar, app, callTFn, uset, prim}) =
        fn Exists (params, body) => exists (params, concrCata alg body)
         | ForAll (param, body) => forAll (param, concrCata alg body)
         | Arrow (arr, {domain, codomain}) =>
            arrow (arr, {domain = concrCata alg domain, codomain = concrCata alg codomain})
         | Record row => record (concrCata alg row)
         | RowExt {base, field = (label, fieldt)} =>
            rowExt {base = concrCata alg base, field = (label, concrCata alg fieldt)}
         | EmptyRow => emptyRow
         | Type args => typ (concrCata alg args)
         | SVar args => svar args
         | App {callee, args} =>
            app {callee = concrCata alg callee, args = Vector.map (concrCata alg) args}
         | CallTFn (name, args) => callTFn (name, Vector.map (concrCata alg) args)
         | UseT args => uset args
         | Prim args => prim args

    fun concrOccurs svarOcc sv = concrCata { exists = #2
                                           , forAll = #2
                                           , arrow = fn (_, {domain, codomain}) => domain orelse codomain
                                           , record = Fn.identity
                                           , rowExt = fn {base, field = (_, fieldt)} => base orelse fieldt
                                           , emptyRow = false
                                           , typ = Fn.identity
                                           , svar = fn sv' => svarOcc sv sv'
                                           , app = fn {callee, args} =>
                                              callee orelse Vector.exists Fn.identity args
                                           , callTFn = fn (_, args) => Vector.exists Fn.identity args
                                           , uset = Fn.constantly false
                                           , prim = Fn.constantly false }

    (* OPTIMIZE: Entire subtrees where the `name` does not occur could be reused. *)
    fun concrSubstitute svarSubst mapping =
        let fun subst mapping =
                fn t as Exists (params, _) | t as ForAll (params, _) =>
                    let val mapping = Vector.foldl (fn ({var, ...}, mapping) =>
                                                        (#1 (Id.SortedMap.remove (mapping, var)))
                                                        handle _ => mapping)
                                                   mapping params
                    in mapConcrChildren (subst mapping) t
                    end
                 | t as (Arrow _ | Record _ | RowExt _ | EmptyRow | App _ | CallTFn _ | Prim _) =>
                    mapConcrChildren (subst mapping) t
                 | Type t => Type (subst mapping t)
                 | t as UseT {var, ...} => getOpt (Id.SortedMap.find (mapping, var), t)
                 | t as SVar sv => getOpt (svarSubst mapping sv, t)
        in subst mapping
        end

    val rec smallConcr =
        fn Exists (params, body) | ForAll (params, body) =>
            Vector.length params = 0 andalso smallConcr body
         | Arrow (_, {domain, codomain}) =>
            smallConcr domain andalso smallConcr codomain
         | Record t => smallConcr t
         | RowExt {base, field = (_, fieldt)} =>
            smallConcr base andalso smallConcr fieldt
         | EmptyRow => true
         | Type t => smallConcr t
         | App {callee, args} => smallConcr callee andalso Vector.all smallConcr args
         | CallTFn (_, args) => Vector.all smallConcr args
         | SVar _ | UseT _ | Prim _ => true

    val rec piEffect =
        fn ForAll (_, body) => piEffect body
         | Arrow (Cst.Implicit, {domain = _, codomain}) => piEffect codomain
         | Arrow (Cst.Explicit eff, _) => SOME eff
         | _ => NONE

    val rec rowExtBase =
        fn RowExt {base, ...} => rowExtBase base
         | t => t

    val app = (* HACK *)
        fn {callee, args = #[]} => callee
         | args => App args

    structure Concr = struct
        val toDoc = concrToDoc
        fun toString svarToDoc = PPrint.pretty 80 o toDoc svarToDoc
        val mapChildren = mapConcrChildren
        val occurs = concrOccurs
        val substitute = concrSubstitute
        val isSmall = smallConcr

        fun rewriteRow label row =
            let val rec rewrite = 
                    fn (RowExt (row as {base, field = (flabel, ftype)})) =>
                        if flabel = label
                        then SOME row
                        else Option.map (fn {base, field} =>
                                             {base = RowExt {base, field = (flabel, ftype)}, field})
                                        (rewrite base)
                     | _ => NONE
            in rewrite row
            end

        fun kindOf svarKind (typeFnKind: Name.t -> tfn_sig) =
            fn t as (ForAll _ | Arrow _ | Record _ | Type _ | Prim _)  => TypeK
             | t as (RowExt _ | EmptyRow) => RowK
             | CallTFn ( callee, #[]) => #kind (typeFnKind callee)
             | UseT {kind, ...} => kind
             | SVar args => svarKind args
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

    datatype effect = datatype FType.effect
    type arrow = FType.arrow

    datatype concr' = datatype FType.concr
    datatype co' = datatype FType.co

    type sv
    type concr = sv FType.concr
    type co = sv FType.co

    val kindToDoc: kind -> PPrint.t
    val defToDoc: def -> PPrint.t
    val arrowDoc: arrow -> PPrint.t
    val svarToDoc: sv -> PPrint.t
    val rowExtBase: concr -> concr

    structure Concr: sig
        datatype t = datatype concr

        val toDoc: concr -> PPrint.t
        val substitute: (ScopeId.t -> bool) ->concr Id.SortedMap.map -> concr -> concr
    end

    structure Co: sig
        val toDoc: co -> PPrint.t
    end
end

