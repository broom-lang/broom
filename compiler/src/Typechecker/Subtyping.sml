structure Subtyping :> sig
    type coercion = (TypecheckingCst.typ FAst.Term.expr -> TypecheckingCst.typ FAst.Term.expr) option
   
    val applyCoercion: coercion -> TypecheckingCst.typ FAst.Term.expr -> TypecheckingCst.typ FAst.Term.expr
    val subType: TypecheckingCst.env -> TypecheckingCst.expr
                 -> TypecheckingCst.typ * TypecheckingCst.typ -> coercion
end = struct
    datatype predicativity = datatype TypeVars.predicativity
    structure TC = TypecheckingCst
    structure FType = FAst.Type
    structure FTerm = FAst.Term
    open TypeError

    type coercion = (TC.typ FTerm.expr -> TC.typ FTerm.expr) option
    type field_coercion = Name.t * (TC.typ FTerm.expr -> TC.typ FTerm.expr)

    fun applyCoercion (coerce: coercion) expr =
        case coerce
        of SOME f => f expr
         | NONE => expr

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
    fun assign env (y, uv: (TC.env, TC.typ) TypeVars.uv, t: TC.typ): unit =
        if TC.uvInScope (env, uv)
        then if TC.occurs uv t
             then raise TypeError (Occurs (uv, t))
             else doAssign env y (uv, t)
        else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv))

    and doAssign env y (uv, typ) =
        case typ
        of TC.InputType _ => raise Fail "unreachable"
         | TC.OutputType t =>
            (case t
             of FType.Arrow (pos, domains) => doAssignArrow env y uv pos domains
              | FType.Prim _ => TypeVars.uvSet (uv, typ))
         | TC.UVar (_, uv') => doAssignUv env y (uv, uv')
         | TC.OVar _ => TypeVars.uvSet (uv, typ)

    and doAssignArrow env y uv pos {domain, codomain} =
        let val domainUv = TypeVars.freshUv env Predicative
            val codomainUv = TypeVars.freshUv env Predicative
            val t' = FType.Arrow (pos, { domain = TC.UVar (pos, domainUv)
                                       , codomain = TC.UVar (pos, codomainUv)})
        in TypeVars.uvSet (uv, TC.OutputType t')
         ; assign env (flipY y, domainUv, domain) (* contravariance *)
         ; assign env (y, codomainUv, codomain)
        end

    and doAssignUv env y (uv, uv') = case TypeVars.uvGet uv'
                                       of Either.Left uv' => TC.uvMerge (uv, uv')
                                        | Either.Right t => doAssign env y (uv, t)

    (* Check that `typ` <: `superTyp` and return the coercion if any. *)
    fun subType env expr (typ: TC.typ, superTyp: TC.typ): coercion =
        case (typ, superTyp)
        of (TC.OutputType t, TC.OutputType t') =>
            (case (t, t')
             of (FType.ForAll _, _) => raise Fail "unimplemented"
              | (_, FType.ForAll _) => raise Fail "unimplemented"
              | (FType.Arrow (_, arr), FType.Arrow (_, arr')) => subArrows env expr (arr, arr')
              | (FType.Record (_, row), FType.Record (_, row')) => 
                 (case subRows env expr (row, row')
                  of [] => NONE)
              | (FType.RowExt _, FType.RowExt _) =>
                ( subRows env expr (typ, superTyp)
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
              | (FType.UseT _, _) => raise Fail "unimplemented"
              | (_, FType.UseT _) => raise Fail "unimplemented"
              | _ => raise TypeError (NonSubType (expr, typ, superTyp)))
         | (TC.UVar (_, uv), TC.UVar (_, uv')) => subUvs env expr (uv, uv')
         | (TC.UVar (_, uv), _) => subUv env expr uv superTyp
         | (_, TC.UVar (_, uv)) => superUv env expr uv typ

    and subArrows env expr ({domain, codomain}, {domain = domain', codomain = codomain'}) =
        let val coerceDomain = subType env expr (domain', domain)
            val coerceCodomain = subType env expr (codomain, codomain')
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

    and subRows env expr (rows: TC.typ * TC.typ): field_coercion list =
        let val rec subExts =
                fn (row, TC.OutputType (FType.RowExt (_, {field = (label, fieldt'), ext = ext'}))) =>
                    let val (fieldt, ext) = reorderRow expr label (TC.Type.rowExtTail ext') row
                        val coerceField = subType env expr (fieldt, fieldt')
                        val coerceExt = subExts (ext, ext')
                    in case coerceField
                       of SOME coerceField => (label, coerceField) :: coerceExt
                        | NONE => coerceExt
                    end
                 | rows => (subType env expr rows; [])
        in subExts rows
        end

    and reorderRow expr label (tail: TC.typ): TC.typ -> TC.typ * TC.typ =
        fn TC.OutputType (FType.RowExt (pos, {field = (label', fieldt'), ext = ext})) =>
            if label = label'
            then (fieldt', ext)
            else let val (fieldt, ext) = reorderRow expr label tail ext
                 in (fieldt, TC.OutputType (FType.RowExt (pos, {field = (label', fieldt'), ext = ext})))
                 end
         (* FIXME: `t` is actually row tail, not the type of `expr`. *)
         | t as TC.OutputType _ => raise TypeError (MissingField (expr, t, label))

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
         | (Either.Left uv, Either.Right t) => ( assign env (Sub, uv, t); NONE )
         | (Either.Right t, Either.Left uv) => ( assign env (Super, uv, t); NONE )
         | (Either.Right t, Either.Right t') => subType env expr (t, t')

    and subUv env expr uv superTyp = case TypeVars.uvGet uv
                                       of Either.Left uv => (assign env (Sub, uv, superTyp); NONE)
                                        | Either.Right t => subType env expr (t, superTyp)

    and superUv env expr uv subTyp = case TypeVars.uvGet uv
                                       of Either.Left uv => (assign env (Super, uv, subTyp); NONE)
                                        | Either.Right t => subType env expr (subTyp, t)
end

