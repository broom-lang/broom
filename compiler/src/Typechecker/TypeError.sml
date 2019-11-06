signature TYPE_ERROR = sig
    datatype t = NonSubType of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.concr * t option
               | NonUnifiable of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.concr * t option
               | InequalKinds of Pos.span * FlexFAst.Type.kind * FlexFAst.Type.kind
               | NonMonotype of Pos.span * FlexFAst.Type.concr
               | UnCallable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnDottable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnboundVal of Pos.span * Name.t
               | TypeCtorArity of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.kind * int
               | OutsideScope of Pos.span * Name.t
               | MissingField of Pos.span * FlexFAst.Type.concr * Name.t
               | DuplicateBinding of Pos.span * Name.t
               | Occurs of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.concr
   
    exception TypeError of t

    val toDoc: Pos.sourcemap -> t -> PPrint.t
end

structure TypeError :> TYPE_ERROR = struct
    structure FAst = FlexFAst
    structure Concr = FAst.Type.Concr
    structure FTerm = FAst.Term
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    datatype t = NonSubType of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.concr * t option
               | NonUnifiable of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.concr * t option
               | InequalKinds of Pos.span * FlexFAst.Type.kind * FlexFAst.Type.kind
               | NonMonotype of Pos.span * FlexFAst.Type.concr
               | UnCallable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnDottable of FlexFAst.Term.expr * FlexFAst.Type.concr
               | UnboundVal of Pos.span * Name.t
               | TypeCtorArity of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.kind * int
               | OutsideScope of Pos.span * Name.t
               | MissingField of Pos.span * FlexFAst.Type.concr * Name.t
               | DuplicateBinding of Pos.span * Name.t
               | Occurs of Pos.span * FlexFAst.Type.concr * FlexFAst.Type.concr
    
    exception TypeError of t

    fun toDoc sourcemap err =
        let val (pos, details) = case err
                                 of NonSubType (pos, typ, superTyp, cause) =>
                                     ( pos
                                     , Concr.toDoc typ <+> text "is not a subtype of" <+> Concr.toDoc superTyp
                                           <> Option.mapOr (fn cause => PPrint.newline <> text "because" <+> toDoc sourcemap cause)
                                                           PPrint.empty cause )
                                  | NonUnifiable (pos, lt, rt, cause) =>
                                     ( pos
                                     , Concr.toDoc lt <+> text "does not unify with" <+> Concr.toDoc rt
                                           <> Option.mapOr (fn cause => PPrint.newline <> text "because" <+> toDoc sourcemap cause)
                                                           PPrint.empty cause )
                                  | InequalKinds (pos, kind, kind') =>
                                     ( pos
                                     , text "kind" <+> FType.kindToDoc kind <+> text "is not equal to" <+> FType.kindToDoc kind' )
                                  | NonMonotype (pos, t) =>
                                     ( pos
                                     , Concr.toDoc t <+> text "is large and not allowed here" )
                                  | UnCallable (expr, typ) =>
                                     ( FTerm.exprPos expr
                                     , text "Value" <+> FTerm.exprToDoc expr
                                           <+> text "of type" <+> Concr.toDoc typ <+> text "can not be called." )
                                  | UnDottable (expr, typ) =>
                                     ( FTerm.exprPos expr
                                     , text "Value" <+> FTerm.exprToDoc expr
                                           <+> text "of type" <+> Concr.toDoc typ <+> text "is not a record or module." )
                                  | UnboundVal (pos, name) => (pos, text "Unbound variable" <+> Name.toDoc name <> text ".")
                                  | TypeCtorArity (pos, calleeType, calleeKind, argc) =>
                                     ( pos
                                     , Concr.toDoc calleeType <+> text ":" <+> FType.kindToDoc calleeKind
                                       <+> text "applied to too many arguments" <+> PPrint.parens (PPrint.int argc) )
                                  | OutsideScope (pos, name) => (pos, text "Type out of scope" <+> Name.toDoc name <> text ".")
                                  | MissingField (pos, typ, label) =>
                                     ( pos
                                     , Concr.toDoc typ <+> text "does not have field"
                                           <+> Name.toDoc label)
                                  | DuplicateBinding (pos, name) =>
                                     (pos, text "Duplicate binding for" <+> Name.toDoc name)
                                  | Occurs (pos, v, t) =>
                                     ( pos
                                     , text "Occurs check: unifying" <+> Concr.toDoc v
                                           <+> text "with" <+> Concr.toDoc t <+> text "would create infinite type." )
        in text "TypeError in" <+> text (Pos.spanToString sourcemap pos) <> text ":" <+> details
        end
end

