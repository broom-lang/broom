signature TYPE_ERROR = sig
    datatype t = NonSubType of TypecheckingCst.expr * TypecheckingCst.typ * TypecheckingCst.typ
               | UnCallable of TypecheckingCst.typ FAst.Term.expr * TypecheckingCst.typ
               | UnDottable of TypecheckingCst.typ FAst.Term.expr * TypecheckingCst.typ
               | UnboundVal of Pos.t * Name.t
               | MissingField of TypecheckingCst.expr * TypecheckingCst.typ * Name.t
               | Occurs of TypecheckingCst.uv * TypecheckingCst.typ
   
    exception TypeError of t

    val toDoc: t -> PPrint.t
end

structure TypeError :> TYPE_ERROR = struct
    structure TC = TypecheckingCst
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    datatype t = NonSubType of TypecheckingCst.expr * TypecheckingCst.typ * TypecheckingCst.typ
               | UnCallable of TypecheckingCst.typ FAst.Term.expr * TypecheckingCst.typ
               | UnDottable of TypecheckingCst.typ FAst.Term.expr * TypecheckingCst.typ
               | UnboundVal of Pos.t * Name.t
               | MissingField of TypecheckingCst.expr * TypecheckingCst.typ * Name.t
               | Occurs of TypecheckingCst.uv * TypecheckingCst.typ
    
    exception TypeError of t

    fun toDoc err =
        let val (pos, details) = case err
                                 of NonSubType (expr, typ, superTyp) =>
                                     ( TC.Expr.pos expr
                                     , text "Value" <+> TC.Expr.toDoc expr
                                           <+> text "of type" <+> TC.Type.toDoc typ <+> text "is not subtype of"
                                           <+> TC.Type.toDoc superTyp)
                                  | UnCallable (expr, typ) =>
                                     ( FAst.Term.exprPos expr
                                     , text "Value" <+> FAst.Term.exprToDoc TC.Type.toDoc expr
                                           <+> text "of type" <+> TC.Type.toDoc typ <+> text "can not be called." )
                                  | UnDottable (expr, typ) =>
                                     ( FAst.Term.exprPos expr
                                     , text "Value" <+> FAst.Term.exprToDoc TC.Type.toDoc expr
                                           <+> text "of type" <+> TC.Type.toDoc typ <+> text "is not a record or module." )
                                  | UnboundVal (pos, name) => (pos, text "Unbound variable" <+> Name.toDoc name <> text ".")
                                  | MissingField (expr, typ, label) =>
                                     ( TC.Expr.pos expr
                                     , text "Value" <+> TC.Expr.toDoc expr
                                           <+> text "of type" <+> TC.Type.toDoc typ <+> text "does not have field"
                                           <+> Name.toDoc label)
                                  | Occurs (uv, t) =>
                                     ( TC.Type.pos t
                                     , text "Occurs check: unifying" <+> Name.toDoc (TypeVars.uvName uv)
                                           <+> text "with" <+> TC.Type.toDoc t <+> text "would create infinite type." )
        in text "TypeError in" <+> Pos.toDoc pos <> text ":" <+> details
        end
end

