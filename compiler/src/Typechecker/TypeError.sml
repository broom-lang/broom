signature TYPE_ERROR = sig
    datatype t = NonSubType of Pos.t * FlexFAst.Type.abs * FlexFAst.Type.abs
               | NonUnifiable of Pos.t * FlexFAst.Type.abs * FlexFAst.Type.abs
               | UnCallable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnDottable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnboundVal of Pos.t * Name.t
               | MissingField of Pos.t * FlexFAst.Type.concr * Name.t
               | Occurs of FlexFAst.Type.concr * FlexFAst.Type.abs
   
    exception TypeError of t

    val toDoc: t -> PPrint.t
end

structure TypeError :> TYPE_ERROR = struct
    structure FAst = FlexFAst
    structure Concr = FAst.Type.Concr
    structure Abs = FAst.Type.Abs
    structure FTerm = FAst.Term
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    datatype t = NonSubType of Pos.t * FlexFAst.Type.abs * FlexFAst.Type.abs
               | NonUnifiable of Pos.t * FlexFAst.Type.abs * FlexFAst.Type.abs
               | UnCallable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnDottable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnboundVal of Pos.t * Name.t
               | MissingField of Pos.t * FlexFAst.Type.concr * Name.t
               | Occurs of FlexFAst.Type.concr * FlexFAst.Type.abs
    
    exception TypeError of t

    fun toDoc err =
        let val (pos, details) = case err
                                 of NonSubType (pos, typ, superTyp) =>
                                     ( pos
                                     , Abs.toDoc typ <+> text "is not a subtype of" <+> Abs.toDoc superTyp )
                                  | NonUnifiable (pos, lt, rt) =>
                                     ( pos
                                     , Abs.toDoc lt <+> text "does not unify with" <+> Abs.toDoc rt )
                                  | UnCallable (expr, typ) =>
                                     ( FTerm.exprPos expr
                                     , text "Value" <+> FTerm.exprToDoc expr
                                           <+> text "of type" <+> Concr.toDoc typ <+> text "can not be called." )
                                  | UnDottable (expr, typ) =>
                                     ( FTerm.exprPos expr
                                     , text "Value" <+> FTerm.exprToDoc expr
                                           <+> text "of type" <+> Concr.toDoc typ <+> text "is not a record or module." )
                                  | UnboundVal (pos, name) => (pos, text "Unbound variable" <+> Name.toDoc name <> text ".")
                                  | MissingField (pos, typ, label) =>
                                     ( pos
                                     , Concr.toDoc typ <+> text "does not have field"
                                           <+> Name.toDoc label)
                                  | Occurs (v, t) =>
                                     ( Abs.pos t
                                     , text "Occurs check: unifying" <+> Concr.toDoc v
                                           <+> text "with" <+> Abs.toDoc t <+> text "would create infinite type." )
        in text "TypeError in" <+> text (Pos.toString pos) <> text ":" <+> details
        end
end

