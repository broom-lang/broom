structure TypecheckFAst :> sig
    structure Term: FAST_TERM where type stmt = FAst.Term.stmt
    structure Type: FAST_TYPE

    datatype error = TypeMismatch of Type.t * Type.t
                   | KindMismatch of Type.kind * Type.kind
                   | UnCallable of Term.expr * Type.t
                   | UnTCallable of Term.expr * Type.t

    val errorToString: error -> string

    val typecheck: Term.stmt vector -> (error, unit) Either.t
end = struct
    structure Term = FAst.Term
    structure Type = FAst.Type

    datatype error = TypeMismatch of Type.t * Type.t
                   | KindMismatch of Type.kind * Type.kind
                   | UnCallable of Term.expr * Type.t
                   | UnTCallable of Term.expr * Type.t

    val errorToString =
        fn TypeMismatch (expected, actual) =>
            "TypeMismatch: " ^ Type.toString expected ^ " " ^ Type.toString actual
         | KindMismatch (expected, actual) =>
            "KindMismatch: " ^ Type.kindToString expected ^ " " ^ Type.kindToString actual
         | UnCallable (expr, typ) =>
            "UnCallable: " ^ Term.exprToString expr ^ ": " ^ Type.toString typ
         | UnTCallable (expr, typ) =>
            "UnTCallable: " ^ Term.exprToString expr ^ ": " ^ Type.toString typ

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
            (* FIXME: arg is not substituted / added to env for param. *)
            (case check callee
             of Type.ForAll (_, {kind = domainKind, ...}, codomain) =>
                 let val argKind = checkKind arg
                 in if Type.kindEq (argKind, domainKind)
                    then codomain
                    else raise TypeError (KindMismatch (domainKind, argKind))
                 end
              | calleeKind => raise TypeError (UnTCallable (callee, calleeKind)))
         | Term.Let (_, stmts, body) =>
            ( Vector.app checkStmt stmts
            ; check body )
         | Term.Use (_, {typ, ...}) => typ
         | Term.Const (pos, c) => Type.Prim (pos, checkConst c)

    and checkStmt = fn Term.Def (_, _, expr) => (check expr; ())

    fun typecheck program =
        Either.Right (Vector.app checkStmt program)
        handle TypeError err => Either.Left err
end
