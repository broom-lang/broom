structure PatternMatching :> sig
    val implement : FAst.Term.program -> FAst.Term.program
end = struct
    structure FTerm = FAst.Term
    datatype expr = datatype FTerm.expr
    datatype stmt = datatype FTerm.stmt
    datatype pat = datatype FTerm.pat

    fun mapExprs f =
        fn Fn (pos, param, arr, body) => Fn (pos, param, arr, f body)
         | TFn (pos, params, body) => TFn (pos, params, f body)
         | With (pos, t, {base, field = (label, fielde)}) =>
            With (pos, t, {base = f base, field = (label, f fielde)})
         | Without (pos, t, {base, field}) => Without (pos, t, {base = f base, field})
         | Where (pos, t, {base, field = (label, fielde)}) =>
            Where (pos, t, {base = f base, field = (label, f fielde)})
         | App (pos, t, {callee, arg}) =>
            App (pos, t, {callee = f callee, arg = f arg})
         | TApp (pos, t, {callee, args}) => TApp (pos, t, {callee = f callee, args})
         | PrimApp (pos, t, opn, targs, args, clauses) =>
            PrimApp ( pos, t, opn, targs, Vector.map f args
                    , Option.map (fn ({def, body}, failure) => ({def, body = f body}, f failure))
                                 clauses )
         | Field (pos, t, expr, label) => Field (pos, t, f expr, label)
         | Letrec (pos, stmts, body) =>
            Letrec (pos, Vector1.map (mapStmtExprs f) stmts, f body)
         | Let (pos, stmts, body) =>
            Let (pos, Vector1.map (mapStmtExprs f) stmts, f body)
         | Match (pos, t, matchee, clauses) =>
            Match (pos, t, f matchee, Vector.map (mapClauseExprs f) clauses)
         | Cast (pos, t, expr, co) => Cast (pos, t, f expr, co)
         | expr as (EmptyRecord _ | Type _ | Use _ | Const _) => expr

    and mapStmtExprs f =
        fn stmt as Axiom _ => stmt
         | Val (pos, def, expr) => Val (pos, def, f expr)
         | Expr expr => Expr (f expr)

    and mapClauseExprs f {pattern, body} =
        { pattern = mapPatternExprs f pattern
        , body = f body }

    and mapPatternExprs f =
        fn pat as (Def _ | AnyP _ | ConstP _) => pat

    fun exprFold f expr = f (mapExprs (exprFold f) expr)

    fun discriminatingClause {pattern, body = _} =
        case pattern
        of ConstP _ => true
         | AnyP _ => false
         | Def _ => false

    val implementExpr =
         exprFold (fn expr as Match (pos, t, matchee, clauses) =>
                       let val (discriminators, defaults) =
                               VectorExt.splitWith discriminatingClause clauses
                           val (stmt, matchee, default) =
                               if VectorSlice.length defaults > 0
                               then case VectorSlice.sub (defaults, 0)
                                    of clause as {pattern = AnyP _, ...} =>
                                        (NONE, matchee, clause)
                                     | {pattern = Def (pos, def), body} =>
                                        ( SOME (Val (pos, def, matchee))
                                        , Use (FTerm.exprPos matchee, def)
                                        , {pattern = AnyP pos, body} )
                               else ( NONE
                                    , matchee
                                    , { pattern = AnyP pos
                                      , body = PrimApp (pos, t, Primop.Panic, #[t], #[], NONE) } )
                           val match = Match ( pos, t, matchee
                                             , VectorExt.append (VectorSlice.vector discriminators, default) )
                       in case stmt
                          of SOME stmt => Let (pos, Vector1.singleton stmt, match)
                           | NONE => match
                       end
                    | expr => expr)

    val implementDefn = mapStmtExprs implementExpr

    fun implement {typeFns, code, sourcemap} =
        case implementExpr (Let code)
        of Let code => {typeFns, code, sourcemap}
         | _ => raise Fail "unreachable"
end

