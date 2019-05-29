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

    datatype 'typ typ = ForAll of Pos.t * def * 'typ
                      | Exists of Pos.t * def * 'typ
                      | Arrow of Pos.t * {domain: 'typ, codomain: 'typ}
                      | Record of Pos.t * 'typ
                      | RowExt of Pos.t * {field: Name.t * 'typ, ext: 'typ}
                      | EmptyRow of Pos.t
                      | Type of Pos.t * 'typ
                      | UseT of Pos.t * def
                      | Prim of Pos.t * Prim.t

    val rec kindToDoc =
        fn TypeK _ => text "Type"
         | ArrowK (_, {domain, codomain}) =>
            kindToDoc domain <+> text "->" <+> kindToDoc codomain

    fun defToDoc {var, kind} = Name.toDoc var <> text ":" <+> kindToDoc kind

    fun toDoc toDoc =
        fn ForAll (_, param, t) =>
            text "forall" <+> defToDoc param <+> text "." <+> toDoc t
         | Exists (_, param, t) =>
            text "exists" <+> defToDoc param <+> text "." <+> toDoc t
         | Arrow (_, {domain, codomain}) =>
            toDoc domain <+> text "->" <+> toDoc codomain
         | Record (_, row) => braces (toDoc row)
         | RowExt (_, {field = (label, fieldType), ext}) =>
            Name.toDoc label <> text ":" <+> toDoc fieldType <+> text "|" <+> toDoc ext
         | EmptyRow _ => text "(||)"
         | Type (_, t) => brackets (text "=" <+> toDoc t)
         | UseT (_, def) => defToDoc def 
         | Prim (_, p) => Prim.toDoc p

    fun toString toDoc = PPrint.pretty 80 o toDoc

    val pos =
        fn ForAll (pos, _, _) => pos
         | Exists (pos, _, _) => pos
         | Arrow (pos, _) => pos
         | Record (pos, _) => pos
         | RowExt (pos, _) => pos
         | EmptyRow pos => pos
         | Type (pos, _) => pos
         | UseT (pos, _) => pos
         | Prim (pos, _) => pos

    fun shallowFoldl f acc =
        fn ForAll (_, _, t) => f (t, acc)
         | Exists (_, _, t) => f (t, acc)
         | Arrow (_, {domain, codomain}) => f (codomain, f (domain, acc))
         | Record (_, row) => f (row, acc)
         | RowExt (_, {field = (_, fieldt), ext}) => f (ext, f (fieldt, acc))
         | EmptyRow _ => acc
         | Type (_, t) => f (t, acc)
         | UseT _ | Prim _ => acc

    fun substitute (fix: 'typ typ -> 'typ) (substituteFixed: Name.t * 'typ -> 'typ -> 'typ)
                   (kv as (name: Name.t, t': 'typ)) (t: 'typ typ): 'typ =
        let val substFixed = substituteFixed kv
            val rec subst =
                fn t as ForAll (pos, param as {var, kind = _}, body) =>
                    fix (if var = name then t else ForAll (pos, param, substFixed body))
                 | t as Exists (pos, param as {var, kind = _}, body) =>
                    fix (if var = name then t else Exists (pos, param, substFixed body))
                 | Arrow (pos, {domain, codomain}) =>
                    fix (Arrow (pos, {domain = substFixed domain, codomain = substFixed codomain}))
                 | Record (pos, row) => fix (Record (pos, substFixed row))
                 | RowExt (pos, {field = (label, fieldt), ext}) =>
                    fix (RowExt (pos, {field = (label, substFixed fieldt), ext = substFixed ext}))
                 | Type (pos, t) => fix (Type (pos, substFixed t))
                 | t as UseT (pos, {var, kind}) => if var = name then t' else fix t
                 | t as (EmptyRow _ | Prim _) => fix t
        in subst t
        end

    fun rowExtTail {tail, wrap} =
        fn RowExt (_, {ext, ...}) => tail ext
         | t => wrap t

    fun unit pos = Prim (pos, Prim.Unit)
end

