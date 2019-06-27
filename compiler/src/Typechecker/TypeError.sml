signature TYPE_ERROR = sig
    datatype t = NonSubType of Pos.t * FlexFAst.Type.abs * FlexFAst.Type.abs
               | UnCallable of FlexFAst.Type.sv FAst.Term.expr * FlexFAst.Type.concr
               | UnDottable of FlexFAst.Type.sv FAst.Term.expr * FlexFAst.Type.concr
               | UnboundVal of Pos.t * Name.t
               | MissingField of Pos.t * FlexFAst.Type.concr * Name.t
               | Occurs of FlexFAst.Type.uv * FlexFAst.Type.abs
   
    exception TypeError of t

    val toDoc: t -> PPrint.t
end

structure TypeError :> TYPE_ERROR = struct
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    datatype t = NonSubType of Pos.t * FlexFAst.Type.abs * FlexFAst.Type.abs
               | UnCallable of FlexFAst.Type.sv FAst.Term.expr * FlexFAst.Type.concr
               | UnDottable of FlexFAst.Type.sv FAst.Term.expr * FlexFAst.Type.concr
               | UnboundVal of Pos.t * Name.t
               | MissingField of Pos.t * FlexFAst.Type.concr * Name.t
               | Occurs of FlexFAst.Type.uv * FlexFAst.Type.abs
    
    exception TypeError of t

    fun toDoc err =
        let val (pos, details) = case err
                                 of NonSubType (pos, typ, superTyp) =>
                                     ( pos
                                     ,  FlexFAst.Type.Abs.toDoc typ <+> text "is not a subtype of" <+> FlexFAst.Type.Abs.toDoc superTyp)
                                  | UnCallable (expr, typ) =>
                                     ( FAst.Term.exprPos expr
                                     , text "Value" <+> FAst.Term.exprToDoc FlexFAst.Type.svarToDoc expr
                                           <+> text "of type" <+> FlexFAst.Type.Concr.toDoc typ <+> text "can not be called." )
                                  | UnDottable (expr, typ) =>
                                     ( FAst.Term.exprPos expr
                                     , text "Value" <+> FAst.Term.exprToDoc FlexFAst.Type.svarToDoc expr
                                           <+> text "of type" <+> FlexFAst.Type.Concr.toDoc typ <+> text "is not a record or module." )
                                  | UnboundVal (pos, name) => (pos, text "Unbound variable" <+> Name.toDoc name <> text ".")
                                  | MissingField (pos, typ, label) =>
                                     ( pos
                                     , FlexFAst.Type.Concr.toDoc typ <+> text "does not have field"
                                           <+> Name.toDoc label)
                                  | Occurs (uv, t) =>
                                     ( FAst.Type.Abs.pos t
                                     , text "Occurs check: unifying" <+> text "^" <> Name.toDoc (TypeVars.Uv.name uv)
                                           <+> text "with" <+> FlexFAst.Type.Abs.toDoc t <+> text "would create infinite type." )
        in text "TypeError in" <+> Pos.toDoc pos <> text ":" <+> details
        end
end

