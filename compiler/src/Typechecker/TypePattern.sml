structure TypePattern = struct
    structure Id = FType.Id
    structure Concr = FlexFAst.Type.Concr
    structure FTerm = FlexFAst.Term
    structure Env = TypecheckingEnv
    structure Uv = TypeVars.Uv

    datatype kind = datatype Kind.t
    datatype effect = datatype FType.effect
    datatype arrow = datatype Cst.explicitness
    datatype concr' = datatype FType.concr
    type concr = FlexFAst.Type.concr
    datatype sv = datatype FlexFAst.Type.sv
    datatype error = datatype TypeError.t
    datatype either = datatype Either.t

    val op|> = Fn.|>

    val nameFromId = Name.fromString o Id.toString

    datatype ('e, 't) pat
        = Callable of 'e * {domain : 't, codomain : 't}
        | HasField of Name.t * 't

    val callable = Callable ((), {domain = (), codomain = ()})

    fun hasField label = HasField (label, ())

    fun coerce env =
        let fun doCoerce pat (expr, ForAll universal) =
                doCoerce pat (applyPolymorphic env universal expr)
              
              | doCoerce pat (expr, Arrow (Implicit, domains as {codomain, ...})) =
                doCoerce pat (applyImplicit domains expr, codomain)

              | doCoerce (pat as Callable _) (expr, SVar (UVar uv)) =
                (case Uv.get env uv
                 of Right typ => doCoerce pat (expr, typ)
                  | Left uv =>
                     let val domain = SVar (UVar (Uv.freshSibling env (uv, TypeK)))
                         val codomain = SVar (UVar (Uv.freshSibling env (uv, TypeK)))
                         val eff = Impure
                         val arrow = {domain, codomain}
                         val typ = Arrow (Explicit eff, arrow)
                         do Uv.set env uv typ
                     in doCoerce pat (expr, typ)
                     end)

              | doCoerce (Callable (er, {domain = dr, codomain = cr}))
                         (expr, Arrow (Explicit eff, {domain, codomain})) =
                (expr, Callable (eff, {domain, codomain}))

              | doCoerce (pat as HasField (label, ())) (expr, SVar (UVar uv)) =
                (case Uv.get env uv
                 of Right typ => doCoerce pat (expr, typ)
                  | Left uv =>
                     let val base = SVar (UVar (Uv.freshSibling env (uv, RowK)))
                         val fieldt = SVar (UVar (Uv.freshSibling env (uv, TypeK)))
                         val typ = Record (RowExt ({base, field = (label, fieldt)}))
                         do Uv.set env uv typ
                     in doCoerce pat (expr, typ)
                     end)

              | doCoerce (HasField (label, ())) (expr, typ as Record row) =
                let val rec fieldType =
                        fn RowExt {base, field = (label', fieldt)} =>
                            if label' = label
                            then fieldt
                            else fieldType base
                         | SVar (UVar uv) =>
                            let val base = SVar (UVar (Uv.freshSibling env (uv, RowK)))
                                val fieldt = SVar (UVar (Uv.freshSibling env (uv, TypeK)))
                                do Uv.set env uv (Record (RowExt ({base, field = (label, fieldt)})))
                            in fieldt
                            end
                         | _ =>
                            ( Env.error env (UnDottable (expr, typ))
                            ; SVar (UVar (Uv.fresh env TypeK)) )
                in (expr, HasField (label, fieldType row))
                end

              | doCoerce _ (_, SVar (Path _)) =
                raise Fail "unimplemented"

              | doCoerce (pat as Callable _) (expr, typ) =
                ( Env.error env (UnCallable (expr, typ))
                ; (expr, Callable (Impure, { domain = SVar (UVar (Uv.fresh env TypeK))
                                           , codomain = typ })) )

              | doCoerce (pat as HasField _) (expr, typ) =
                ( Env.error env (UnDottable (expr, typ))
                ; doCoerce pat (expr, SVar (UVar (Uv.fresh env TypeK))) )
        in doCoerce
        end

    and applyPolymorphic env (params, body) callee =
        let val eff = valOf (FType.piEffect body)
            val (args, mapping) =
                Vector1.foldl (fn (def as {var, kind = _}, (args, mapping)) =>
                                   let val arg = resolveTypeArg env eff def
                                   in (arg :: args, Id.SortedMap.insert (mapping, var, arg))
                                   end)
                              ([], Id.SortedMap.empty) params
            val args = args |> List.rev |> Vector1.fromList |> valOf
            val calleeType = Concr.substitute env mapping body
        in ( FTerm.TApp (FTerm.exprPos callee, calleeType, {callee, args})
           , calleeType )
        end

    and resolveTypeArg env eff {var = _, kind = kind as CallsiteK} =
        (case eff
         of Impure => CallTFn (Env.freshAbstract env kind)
          | Pure => CallTFn (Env.pureCallsite env))

      | resolveTypeArg env _ {var, kind} =
        SVar (UVar (Uv.new env (nameFromId var, kind)))

    and applyImplicit {domain, codomain} callee =
        let val pos = FTerm.exprPos callee
        in FTerm.App (pos, codomain, {callee, arg = Subtyping.resolve pos domain})
        end
end

