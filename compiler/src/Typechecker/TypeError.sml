signature TYPE_ERROR = sig
    datatype t = NonSubType of Pos.span * FlexFAst.Type.abs * FlexFAst.Type.abs * t option
               | NonUnifiable of Pos.span * FlexFAst.Type.abs * FlexFAst.Type.abs * t option
               | UnCallable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnDottable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnboundVal of Pos.span * Name.t
               | OutsideScope of Pos.span * Name.t
               | MissingField of Pos.span * FlexFAst.Type.concr * Name.t
               | Occurs of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.abs
   
    exception TypeError of t

    val toDoc: Pos.sourcemap -> t -> PPrint.t
end

structure TypeError :> TYPE_ERROR = struct
    structure FAst = FlexFAst
    structure Concr = FAst.Type.Concr
    structure Abs = FAst.Type.Abs
    structure FTerm = FAst.Term
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    datatype t = NonSubType of Pos.span * FlexFAst.Type.abs * FlexFAst.Type.abs * t option
               | NonUnifiable of Pos.span * FlexFAst.Type.abs * FlexFAst.Type.abs * t option
               | UnCallable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnDottable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnboundVal of Pos.span * Name.t
               | OutsideScope of Pos.span * Name.t
               | MissingField of Pos.span * FlexFAst.Type.concr * Name.t
               | Occurs of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.abs
    
    exception TypeError of t

    fun toDoc sourcemap err =
        let val (pos, details) = case err
                                 of NonSubType (pos, typ, superTyp, cause) =>
                                     ( pos
                                     , Abs.toDoc typ <+> text "is not a subtype of" <+> Abs.toDoc superTyp
                                           <> Option.mapOr (fn cause => PPrint.newline <> text "because" <+> toDoc sourcemap cause)
                                                           PPrint.empty cause )
                                  | NonUnifiable (pos, lt, rt, cause) =>
                                     ( pos
                                     , Abs.toDoc lt <+> text "does not unify with" <+> Abs.toDoc rt
                                           <> Option.mapOr (fn cause => PPrint.newline <> text "because" <+> toDoc sourcemap cause)
                                                           PPrint.empty cause )
                                  | UnCallable (expr, typ) =>
                                     ( FTerm.exprPos expr
                                     , text "Value" <+> FTerm.exprToDoc expr
                                           <+> text "of type" <+> Concr.toDoc typ <+> text "can not be called." )
                                  | UnDottable (expr, typ) =>
                                     ( FTerm.exprPos expr
                                     , text "Value" <+> FTerm.exprToDoc expr
                                           <+> text "of type" <+> Concr.toDoc typ <+> text "is not a record or module." )
                                  | UnboundVal (pos, name) => (pos, text "Unbound variable" <+> Name.toDoc name <> text ".")
                                  | OutsideScope (pos, name) => (pos, text "Type out of scope" <+> Name.toDoc name <> text ".")
                                  | MissingField (pos, typ, label) =>
                                     ( pos
                                     , Concr.toDoc typ <+> text "does not have field"
                                           <+> Name.toDoc label)
                                  | Occurs (pos, v, t) =>
                                     ( pos
                                     , text "Occurs check: unifying" <+> Concr.toDoc v
                                           <+> text "with" <+> Abs.toDoc t <+> text "would create infinite type." )
        in text "TypeError in" <+> text (Pos.spanToString sourcemap pos) <> text ":" <+> details
        end
end

