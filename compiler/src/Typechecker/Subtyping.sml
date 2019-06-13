structure Subtyping :> sig
    type coercion = (TypecheckingCst.sv FAst.Term.expr -> TypecheckingCst.sv FAst.Term.expr) option
   
    val applyCoercion: coercion -> TypecheckingCst.sv FAst.Term.expr -> TypecheckingCst.sv FAst.Term.expr
    val subType: TypecheckingCst.env -> TypecheckingCst.expr
                 -> TypecheckingCst.abs * TypecheckingCst.abs -> coercion
end = struct
    datatype predicativity = datatype TypeVars.predicativity
    structure TC = TypecheckingCst
    structure FType = FAst.Type
    datatype abs = datatype FType.abs
    structure FTerm = FAst.Term
    open TypeError

    fun idInScope env id = isSome (TC.Env.typeFind env id)

    type coercion = (TC.sv FTerm.expr -> TC.sv FTerm.expr) option
    type field_coercion = Name.t * (TC.sv FTerm.expr -> TC.sv FTerm.expr)

    fun applyCoercion (coerce: coercion) expr =
        case coerce
        of SOME f => f expr
         | NONE => expr

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
    fun assign env (y, uv: (TC.env, TC.concr) TypeVars.uv, t: TC.abs): unit =
        if TC.uvInScope (env, uv)
        then if TC.absOccurs uv t
             then raise TypeError (Occurs (uv, t))
             else doAssign env y (uv, t)
        else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv))

    and doAssign env y (uv, typ: TC.abs) =
        case typ
        of Exists _ => raise Fail "unimplemented"
         | Concr t =>
            (case t
             of FType.Arrow (pos, domains) => doAssignArrow env y uv pos domains
              | FType.Prim _ => TypeVars.uvSet (uv, t)
              | FType.UseT (_, {var, ...}) => 
                 if idInScope env var
                 then TypeVars.uvSet (uv, t)
                 else raise Fail ("Opaque type out of scope: g__" ^ Id.toString var)
              | FType.SVar (_, TC.UVar uv') => doAssignUv env y (uv, uv'))

    and doAssignArrow env y uv pos {domain, codomain} =
        let val domainUv = TypeVars.freshUv env Predicative
            val codomainUv = TypeVars.freshUv env Predicative
            val t' = FType.Arrow (pos, { domain = FType.SVar (pos, TC.UVar domainUv)
                                       , codomain = FType.SVar (pos, TC.UVar codomainUv)})
        in TypeVars.uvSet (uv, t')
         ; assign env (flipY y, domainUv, Concr domain) (* contravariance *)
         ; assign env (y, codomainUv, Concr codomain)
        end

    and doAssignUv env y (uv, uv') = case TypeVars.uvGet uv'
                                       of Either.Left uv' => TC.uvMerge (uv, uv')
                                        | Either.Right t => doAssign env y (uv, Concr t)

    (* Check that `typ` <: `superTyp` and return the coercion if any. *)
    fun subType env expr (typ: TC.abs, superTyp: TC.abs): coercion =
        case (typ, superTyp)
        of (Concr t, Concr t') =>
            (case (t, t')
             of (FType.ForAll _, _) => raise Fail "unimplemented"
              | (_, FType.ForAll _) => raise Fail "unimplemented"
              | (FType.Arrow (_, arr), FType.Arrow (_, arr')) => subArrows env expr (arr, arr')
              | (FType.Record (_, row), FType.Record (_, row')) => 
                 (case subRows env expr (row, row')
                  of [] => NONE)
              | (FType.RowExt _, FType.RowExt _) =>
                ( subRows env expr (t, t')
                ; NONE ) (* No values of row type exist => coercion unnecessary *)
              | (FType.EmptyRow _, FType.EmptyRow _) => NONE
              | (FType.Prim (_, pl), FType.Prim (_, pr)) =>
                 if pl = pr
                 then NONE
                 else raise Fail "<:"
              | (FType.Type (pos, t), FType.Type (_, t')) =>
                 ( subType env expr (t, t')
                 ; subType env expr (t', t)
                 ; SOME (fn _ => FTerm.Type (pos, t)))
              | (FType.UseT (_, {var, ...}), FType.UseT (_, {var = var', ...})) =>
                 if var = var'
                 then if idInScope env var
                      then NONE
                      else raise Fail ("Opaque type out of scope: " ^ TC.Type.absToString superTyp)
                 else raise TypeError (NonSubType (expr, typ, superTyp))
              | (FType.SVar (_, TC.UVar uv), FType.SVar (_, TC.UVar uv')) => subUvs env expr (uv, uv')
              | (FType.SVar (_, TC.UVar uv), _) => subUv env expr uv superTyp
              | (_, FType.SVar (_, TC.UVar uv)) => superUv env expr uv typ
              | _ => raise Fail ("unimplemented: " ^ TC.Type.absToString typ ^ " <: "
                                 ^ TC.Type.absToString superTyp))

    and subArrows env expr ({domain, codomain}, {domain = domain', codomain = codomain'}) =
        let val coerceDomain = subType env expr (Concr domain', Concr domain)
            val coerceCodomain = subType env expr (Concr codomain, Concr codomain')
        in if isSome coerceDomain orelse isSome coerceCodomain
           then SOME (fn callee =>
                          let val pos = FTerm.exprPos callee
                              val param = {var = Name.fresh (), typ = domain'}
                              val arg = applyCoercion coerceDomain (FTerm.Use (pos, param))
                              val body = applyCoercion coerceCodomain (FTerm.App (pos, codomain, {callee, arg}))
                          in FTerm.Fn (pos, param, body)
                          end)
           else NONE
        end

    and subRows env expr (rows: TC.concr * TC.concr): field_coercion list =
        let val rec subExts =
                fn (row, FType.RowExt (_, {field = (label, fieldt'), ext = ext'})) =>
                    let val (fieldt, ext) = reorderRow expr label (FType.rowExtTail ext') row
                        val coerceField = subType env expr (Concr fieldt, Concr fieldt')
                        val coerceExt = subExts (ext, ext')
                    in case coerceField
                       of SOME coerceField => (label, coerceField) :: coerceExt
                        | NONE => coerceExt
                    end
                 | rows => (subType env expr (Pair.bimap Concr Concr rows); [])
        in subExts rows
        end

    and reorderRow expr label (tail: TC.concr): TC.concr -> TC.concr * TC.concr =
        fn FType.RowExt (pos, {field = (label', fieldt'), ext = ext}) =>
            if label = label'
            then (fieldt', ext)
            else let val (fieldt, ext) = reorderRow expr label tail ext
                 in (fieldt, FType.RowExt (pos, {field = (label', fieldt'), ext = ext}))
                 end
         (* FIXME: `t` is actually row tail, not the type of `expr`. *)
         | t => raise TypeError (MissingField (expr, t, label))

    and subUvs env expr (uv: TC.uv, uv': TC.uv): coercion =
        case (TypeVars.uvGet uv, TypeVars.uvGet uv')
        of (Either.Left uv, Either.Left uv') =>
            if TC.uvInScope (env, uv)
            then if TC.uvInScope (env, uv')
                 then if TypeVars.uvEq (uv, uv')
                      then NONE
                      else ( TC.uvMerge (uv, uv'); NONE )
                 else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv'))
            else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv'))
         | (Either.Left uv, Either.Right t) => ( assign env (Sub, uv, Concr t); NONE )
         | (Either.Right t, Either.Left uv) => ( assign env (Super, uv, Concr t); NONE )
         | (Either.Right t, Either.Right t') => subType env expr (Concr t, Concr t')

    and subUv env expr uv superTyp = case TypeVars.uvGet uv
                                       of Either.Left uv => (assign env (Sub, uv, superTyp); NONE)
                                        | Either.Right t => subType env expr (Concr t, superTyp)

    and superUv env expr uv subTyp = case TypeVars.uvGet uv
                                       of Either.Left uv => (assign env (Super, uv, subTyp); NONE)
                                        | Either.Right t => subType env expr (subTyp, Concr t)
end

