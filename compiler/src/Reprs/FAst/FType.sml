structure FType = struct
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val brackets = PPrint.brackets
    val braces = PPrint.braces

    structure Prim = PrimType

    datatype kind = ArrowK of Pos.t * {domain: kind, codomain: kind}
                  | TypeK of Pos.t

    type def = {var: Name.t, kind: kind}

    datatype 'sv concr
        = ForAll of Pos.t * def * 'sv concr
        | Arrow of Pos.t * {domain: 'sv concr, codomain: 'sv concr}
        | Record of Pos.t * 'sv concr
        | RowExt of Pos.t * {field: Name.t * 'sv concr, ext: 'sv concr}
        | EmptyRow of Pos.t
        | Type of Pos.t * 'sv abs
        | UseT of Pos.t * def
        | SVar of Pos.t * 'sv
        | Prim of Pos.t * Prim.t
    
    and 'sv abs
        = Exists of Pos.t * def * 'sv abs
        | Concr of 'sv concr

    val rec kindToDoc =
        fn TypeK _ => text "Type"
         | ArrowK (_, {domain, codomain}) =>
            kindToDoc domain <+> text "->" <+> kindToDoc codomain

    fun defToDoc {var, kind} = Name.toDoc var <> text ":" <+> kindToDoc kind

    fun concrToDoc svarToDoc =
        let val rec concrToDoc =
                fn ForAll (_, param, t) =>
                    text "forall" <+> defToDoc param <+> text "." <+> concrToDoc t
                 | Arrow (_, {domain, codomain}) =>
                    concrToDoc domain <+> text "->" <+> concrToDoc codomain
                 | Record (_, row) => braces (concrToDoc row)
                 | RowExt (_, {field = (label, fieldType), ext}) =>
                    Name.toDoc label <> text ":" <+> concrToDoc fieldType <+> text "|" <+> concrToDoc ext
                 | EmptyRow _ => text "(||)"
                 | Type (_, t) => brackets (text "=" <+> absToDoc svarToDoc t)
                 | SVar (_, sv) => svarToDoc sv
                 | UseT (_, {var, kind = _}) => Name.toDoc var
                 | Prim (_, p) => Prim.toDoc p
        in concrToDoc
        end

    and absToDoc svarToDoc =
        let val rec absToDoc =
                fn Exists (_, param, t) => text "exists" <+> defToDoc param <+> text "." <+> absToDoc t
                 | Concr t => concrToDoc svarToDoc t
        in absToDoc
        end

    val rec splitExistentials =
        fn Exists (_, def, body) => let val (defs, body) = splitExistentials body
                                    in (def :: defs, body)
                                    end
         | Concr t => ([], t)

    fun mapConcrChildren f =
        fn ForAll (pos, param, body) => ForAll (pos, param, f body)
         | Arrow (pos, {domain, codomain}) =>
            Arrow (pos, {domain = f domain, codomain = f codomain})
         | Record (pos, row) => Record (pos, f row)
         | RowExt (pos, {field = (label, fieldt), ext}) =>
            RowExt (pos, {field = (label, f fieldt), ext = f ext})
         | t as (EmptyRow _ | Type _ | SVar _ | UseT _ | Prim _) => t

    fun mapAbsChildren f =
        fn Exists (pos, param, t) => Exists (pos, param, f t)
         | t as Concr _ => t

    fun concrCata (alg as {forAll, arrow, record, rowExt, emptyRow, typ, svar, uset, prim}) =
        fn ForAll (pos, param, body) => forAll (pos, param, concrCata alg body)
         | Arrow (pos, {domain, codomain}) =>
            arrow (pos, {domain = concrCata alg domain, codomain = concrCata alg codomain})
         | Record (pos, row) => record (pos, concrCata alg row)
         | RowExt (pos, {field = (label, fieldt), ext}) =>
            rowExt (pos, {field = (label, concrCata alg fieldt), ext = concrCata alg ext})
         | EmptyRow args => emptyRow args
         | Type args => typ args
         | SVar args => svar args
         | UseT args => uset args
         | Prim args => prim args

    fun absCata (alg as {exists, concr}) =
        fn Exists (pos, param, body) => exists (pos, param, absCata alg body)
         | Concr args => concr args

    fun concrOccurs svarOcc sv = concrCata { forAll = #3
                                           , arrow = fn (_, {domain, codomain}) => domain orelse codomain
                                           , record = #2
                                           , rowExt = fn (_, {field = (_, fieldt), ext}) => fieldt orelse ext
                                           , emptyRow = Fn.constantly false
                                           , typ = fn (_, t) => absOccurs svarOcc sv t
                                           , svar = fn (_, sv') => svarOcc sv sv'
                                           , uset = Fn.constantly false
                                           , prim = Fn.constantly false }

    and absOccurs svarOcc sv = absCata { exists = #3
                                       , concr = concrOccurs svarOcc sv }

    (* OPTIMIZE: Entire subtrees where the `name` does not occur could be reused. *)
    fun concrSubstitute svarSubst (kv as (name, t')) =
        let val rec subst =
                fn t as ForAll (pos, param as {var, ...}, body) =>
                    if var = name then t else mapConcrChildren subst t
                 | t as (Arrow _ | Record _ | RowExt _ | EmptyRow _ | Prim _) =>
                    mapConcrChildren subst t
                 | Type (pos, t) => Type (pos, absSubstitute svarSubst kv t)
                 | t as UseT (pos, {var, ...}) => if var = name then t' else t
                 | t as SVar (pos, sv) => getOpt (svarSubst kv sv, t)
        in subst
        end

    and absSubstitute svarSubst (kv as (name, _)) =
        let val rec subst =
                fn t as Exists (pos, param as {var, ...}, body) =>
                    if var = name then t else mapAbsChildren subst body
                 | Concr t => Concr (concrSubstitute svarSubst kv t)
        in subst
        end

    val rec rowExtTail =
        fn RowExt (_, {ext, ...}) => rowExtTail ext
         | t => t

    fun unit pos = Prim (pos, Prim.Unit)

    structure Concr = struct
        val pos =
            fn ForAll (pos, _, _) => pos
             | Arrow (pos, _) => pos
             | Record (pos, _) => pos
             | RowExt (pos, _) => pos
             | EmptyRow pos => pos
             | Type (pos, _) => pos
             | SVar (pos, _) => pos
             | UseT (pos, _) => pos
             | Prim (pos, _) => pos

        val toDoc = concrToDoc
        fun toString svarToDoc = PPrint.pretty 80 o toDoc svarToDoc
        val occurs = concrOccurs
        val substitute = concrSubstitute
    end

    structure Abs = struct
        val pos =
            fn Exists (pos, _, _) => pos
             | Concr t => Concr.pos t

        val toDoc = absToDoc
        fun toString svarToDoc = PPrint.pretty 80 o toDoc svarToDoc
        val occurs = absOccurs
        val substitute = absSubstitute
    end
end

