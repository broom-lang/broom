signature TYPE_ERROR = sig
    datatype t = UnCallable of TypecheckingCst.typ FAst.Term.expr * TypecheckingCst.typ
               | UnboundVal of Pos.t * Name.t
               | Occurs of (TypecheckingCst.scope, TypecheckingCst.typ) TypeVars.uv
                         * TypecheckingCst.typ
   
    exception TypeError of t

    val toDoc: t -> PPrint.t
end

structure TypeError :> TYPE_ERROR = struct
    structure TC = TypecheckingCst
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    datatype t = UnCallable of TypecheckingCst.typ FAst.Term.expr * TypecheckingCst.typ
               | UnboundVal of Pos.t * Name.t
               | Occurs of (TypecheckingCst.scope, TypecheckingCst.typ) TypeVars.uv
                         * TypecheckingCst.typ
    
    exception TypeError of t

    fun toDoc err =
        let val (pos, details) = case err
                                 of UnCallable (expr, typ) =>
                                     ( FAst.Term.exprPos expr
                                     , text "Value" <+> FAst.Term.exprToDoc TC.Type.toDoc expr
                                           <+> text "of type" <+> TC.Type.toDoc typ <+> text "can not be called." )
                                  | UnboundVal (pos, name) => (pos, text "Unbound variable" <+> Name.toDoc name <> text ".")
                                  | Occurs (uv, t) =>
                                     ( TC.Type.pos t
                                     , text "Occurs check: unifying" <+> Name.toDoc (TypeVars.uvName uv)
                                           <+> text "with" <+> TC.Type.toDoc t <+> text "would create infinite type." )
        in text "TypeError in" <+> Pos.toDoc pos <> text ":" <+> details
        end
end

