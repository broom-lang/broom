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
         | Arrow (pos, _) => pos
         | Record (pos, _) => pos
         | RowExt (pos, _) => pos
         | EmptyRow pos => pos
         | Type (pos, _) => pos
         | UseT (pos, _) => pos
         | Prim (pos, _) => pos

    fun shallowFoldl f acc =
        fn ForAll (_, _, t) => f (t, acc)
         | Arrow (_, {domain, codomain}) => f (codomain, f (domain, acc))
         | Record (_, row) => f (row, acc)
         | RowExt (_, {field = (_, fieldt), ext}) => f (ext, f (fieldt, acc))
         | EmptyRow _ => acc
         | Type (_, t) => f (t, acc)
         | UseT _ | Prim _ => acc

    fun rowExtTail {tail, wrap} =
        fn RowExt (_, {ext, ...}) => tail ext
         | t => wrap t
end

