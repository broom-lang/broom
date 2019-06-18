signature TYPE_ERROR = sig
    datatype t = NonSubType of Cst.Term.expr * TypecheckingCst.abs * TypecheckingCst.abs
               | UnCallable of TypecheckingCst.sv FAst.Term.expr * TypecheckingCst.concr
               | UnDottable of TypecheckingCst.sv FAst.Term.expr * TypecheckingCst.concr
               | UnboundVal of Pos.t * Name.t
               | MissingField of Cst.Term.expr * TypecheckingCst.concr * Name.t
               | Occurs of TypecheckingCst.uv * TypecheckingCst.abs
   
    exception TypeError of t

    val toDoc: t -> PPrint.t
end

structure TypeError :> TYPE_ERROR = struct
    structure TC = TypecheckingCst
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    datatype t = NonSubType of Cst.Term.expr * TypecheckingCst.abs * TypecheckingCst.abs
               | UnCallable of TypecheckingCst.sv FAst.Term.expr * TypecheckingCst.concr
               | UnDottable of TypecheckingCst.sv FAst.Term.expr * TypecheckingCst.concr
               | UnboundVal of Pos.t * Name.t
               | MissingField of Cst.Term.expr * TypecheckingCst.concr * Name.t
               | Occurs of TypecheckingCst.uv * TypecheckingCst.abs
    
    exception TypeError of t

    fun toDoc err =
        let val (pos, details) = case err
                                 of NonSubType (expr, typ, superTyp) =>
                                     ( Cst.Term.exprPos expr
                                     , text "Value" <+> Cst.Term.exprToDoc expr
                                           <+> text "of type" <+> TC.Type.absToDoc typ <+> text "is not subtype of"
                                           <+> TC.Type.absToDoc superTyp)
                                  | UnCallable (expr, typ) =>
                                     ( FAst.Term.exprPos expr
                                     , text "Value" <+> FAst.Term.exprToDoc TC.svarToDoc expr
                                           <+> text "of type" <+> TC.Type.concrToDoc typ <+> text "can not be called." )
                                  | UnDottable (expr, typ) =>
                                     ( FAst.Term.exprPos expr
                                     , text "Value" <+> FAst.Term.exprToDoc TC.svarToDoc expr
                                           <+> text "of type" <+> TC.Type.concrToDoc typ <+> text "is not a record or module." )
                                  | UnboundVal (pos, name) => (pos, text "Unbound variable" <+> Name.toDoc name <> text ".")
                                  | MissingField (expr, typ, label) =>
                                     ( Cst.Term.exprPos expr
                                     , text "Value" <+> Cst.Term.exprToDoc expr
                                           <+> text "of type" <+> TC.Type.concrToDoc typ <+> text "does not have field"
                                           <+> Name.toDoc label)
                                  | Occurs (uv, t) =>
                                     ( FAst.Type.Abs.pos t
                                     , text "Occurs check: unifying" <+> text "^" <> Name.toDoc (TypeVars.uvName uv)
                                           <+> text "with" <+> TC.Type.absToDoc t <+> text "would create infinite type." )
        in text "TypeError in" <+> Pos.toDoc pos <> text ":" <+> details
        end
end

