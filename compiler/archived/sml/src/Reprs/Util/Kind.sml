structure Kind :> sig
    datatype t
        = ArrowK of {domain: t, codomain: t}
        | TypeK
        | RowK
        | CallsiteK

    val toDoc: t -> PPrint.t
    val toString: t -> string
end = struct
    val text = PPrint.text
    val op<+> = PPrint.<+>

    datatype t
        = ArrowK of {domain: t, codomain: t}
        | TypeK
        | RowK
        | CallsiteK

    val rec toDoc =
        fn TypeK => text "Type"
         | RowK => text "Row"
         | ArrowK {domain, codomain} => toDoc domain <+> text "->" <+> toDoc codomain
         | CallsiteK => text "Callsite"

    val toString = PPrint.pretty 80 o toDoc
end

