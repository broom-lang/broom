structure TypecheckTerm :> sig
    structure Term: FAST_TERM
    structure Type: FAST_TYPE

    datatype error = TypeMismatch of Type.t * Type.t
                   | KindMismatch of Type.kind * Type.kind
                   | UnCallable of Term.expr * Type.t
                   | UnTCallable of Term.expr * Type.t

    val typecheck: Term.expr -> (error, Type.t) Either.t
end = struct
    structure Term = FAst.Term
    structure Type = FAst.Type

    datatype error = TypeMismatch of Type.t * Type.t
                   | KindMismatch of Type.kind * Type.kind
                   | UnCallable of Term.expr * Type.t
                   | UnTCallable of Term.expr * Type.t

    exception TypeError of error

    fun checkKind _ = Type.TypeK

    val checkConst =
        fn Const.Int _ => Type.Int

    val rec check =
        fn Term.Fn (pos, {typ = domain, ...}, body) =>
            Type.Arrow (pos, {domain, codomain = check body})
         | Term.TFn (pos, def, body) =>
            Type.ForAll (pos, def, check body)
         | Term.App (_, {callee, arg}) =>
            (case check callee
             of Type.Arrow (_, {domain, codomain}) =>
                 let val argType = check arg
                 in if Type.eq (argType, domain)
                    then codomain
                    else raise TypeError (TypeMismatch (domain, argType))
                 end
              | calleeType => raise TypeError (UnCallable (callee, calleeType)))
         | Term.TApp (_, {callee, arg}) =>
            (case check callee
             of Type.ForAll (_, {kind = domainKind, ...}, codomain) =>
                 let val argKind = checkKind arg
                 in if Type.kindEq (argKind, domainKind)
                    then codomain
                    else raise TypeError (KindMismatch (domainKind, argKind))
                 end
              | calleeKind => raise TypeError (UnTCallable (callee, calleeKind)))
         | Term.Use (_, {typ, ...}) => typ
         | Term.Const (pos, c) => Type.Prim (pos, checkConst c)

    fun typecheck expr =
        Either.Right (check expr)
        handle TypeError err => Either.Left err
end
