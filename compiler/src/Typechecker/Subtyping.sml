structure Subtyping :> sig
    type coercion = (TypecheckingCst.typ FAst.Term.expr -> TypecheckingCst.typ FAst.Term.expr) option
   
    val applyCoercion: coercion -> TypecheckingCst.typ FAst.Term.expr -> TypecheckingCst.typ FAst.Term.expr
    val subType: TypecheckingCst.scope -> TypecheckingCst.expr
                 -> TypecheckingCst.typ * TypecheckingCst.typ -> coercion
end = struct
    structure TC = TypecheckingCst
    structure FType = FAst.Type
    structure FTerm = FAst.Term
    open TypeError

    type coercion = (TC.typ FTerm.expr -> TC.typ FTerm.expr) option

    fun applyCoercion (coerce: coercion) expr =
        case coerce
        of SOME f => f expr
         | NONE => expr

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
    fun assign scope (y, uv: (TC.scope, TC.typ) TypeVars.uv, t: TC.typ): unit =
        if TC.uvInScope (scope, uv)
        then if TC.occurs uv t
             then raise TypeError (Occurs (uv, t))
             else doAssign scope y (uv, t)
        else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv))

    and doAssign scope y (uv, typ) =
        case typ
        of TC.InputType _ => raise Fail "unreachable"
         | TC.OutputType t =>
            (case t
             of FType.Arrow (pos, domains) => doAssignArrow scope y uv pos domains
              | FType.Prim _ => TypeVars.uvSet (uv, typ))
         | TC.UVar (_, uv') => doAssignUv scope y (uv, uv')
         | TC.OVar _ => TypeVars.uvSet (uv, typ)

    and doAssignArrow scope y uv pos {domain, codomain} =
        let val domainUv = TypeVars.freshUv scope
            val codomainUv = TypeVars.freshUv scope
            val t' = FType.Arrow (pos, { domain = TC.UVar (pos, domainUv)
                                       , codomain = TC.UVar (pos, codomainUv)})
        in TypeVars.uvSet (uv, TC.OutputType t')
         ; assign scope (flipY y, domainUv, domain) (* contravariance *)
         ; assign scope (y, codomainUv, codomain)
        end

    and doAssignUv scope y (uv, uv') = case TypeVars.uvGet uv'
                                       of Either.Left uv' => TC.uvMerge (uv, uv')
                                        | Either.Right t => doAssign scope y (uv, t)

    (* Check that `typ` <: `superTyp` and return the (mutating) coercion if any. *)
    fun subType scope expr (typ: TC.typ, superTyp: TC.typ): coercion =
        case (typ, superTyp)
        of (TC.OutputType t, TC.OutputType t') =>
            (case (t, t')
             of (FType.Arrow (_, arr), FType.Arrow (_, arr')) => subArrows scope expr (arr, arr')
              | (FType.Record (_, row), FType.Record (_, row')) => subType scope expr (row, row')
              | (FType.RowExt (_, row), FType.RowExt _) => subRowExts scope expr (row, superTyp)
              | (FType.EmptyRow _, FType.EmptyRow _) => NONE
              | (FType.Prim (_, pl), FType.Prim (_, pr)) =>
                 if pl = pr
                 then NONE
                 else raise Fail "<:"
              | (FType.Type (pos, t), FType.Type (_, t')) =>
                 ( subType scope expr (t, t')
                 ; subType scope expr (t', t)
                 ; SOME (fn _ => FTerm.Type (pos, t))))
         | (TC.UVar (_, uv), TC.UVar (_, uv')) => subUvs scope expr (uv, uv')
         | (TC.UVar (_, uv), _) => subUv scope expr uv superTyp
         | (_, TC.UVar (_, uv)) => superUv scope expr uv typ

    and subArrows scope expr ({domain, codomain}, {domain = domain', codomain = codomain'}) =
        let val coerceDomain = subType scope expr (domain', domain)
            val coerceCodomain = subType scope expr (codomain, codomain')
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

    and subRowExts scope expr (row as {field = (label, fieldt), ext}, row') =
        let val (fieldt', ext') = reorderRow expr label (TC.Type.rowExtTail ext) row'
            val coerceField = subType scope expr (fieldt, fieldt')
            val coerceExt = subType scope expr (ext, ext')
        in (* FIXME: This coercion combination assumes this is a record row: *)
           SOME (fn expr =>
                     let val pos = FTerm.exprPos expr
                         val recordTyp = TC.OutputType (FType.Record (pos, TC.OutputType (FType.RowExt (pos, row))))
                         val row' = {field = (label, fieldt'), ext = ext'}
                         val recordTyp' = TC.OutputType (FType.Record (pos, TC.OutputType (FType.RowExt (pos, row'))))
                         val recordDef = {var = Name.fresh (), typ = recordTyp}
                         val recordBind = FTerm.Val (pos, recordDef, expr)
                         val recordRef = FTerm.Use (pos, recordDef)
                         val fieldGet = applyCoercion coerceField (FTerm.Field (pos, fieldt, recordRef, label))
                         val fieldDef = {var = Name.freshen label, typ = fieldt'}
                         val fieldRedef = FTerm.Val (pos, fieldDef, fieldGet)
                         val extTyp = TC.OutputType (FType.Record (pos, ext'))
                         val extGet = applyCoercion coerceExt (FTerm.Use (pos, recordDef))
                         val extRedef = FTerm.Val (pos, {var = Name.fresh (), typ = extTyp}, extGet)
                         val body = FTerm.Extend ( pos, recordTyp'
                                                            , Vector.fromList [(label, FTerm.Use (pos, fieldDef))]
                                                            , SOME (FTerm.Use (pos, recordDef)) )
                     in FTerm.Let (pos, Vector.fromList [recordBind, fieldRedef, extRedef], body)
                     end)
        end

    and reorderRow expr label (tail: TC.typ): TC.typ -> TC.typ * TC.typ =
        fn TC.OutputType (FType.RowExt (pos, {field = (label', fieldt'), ext = ext})) =>
            if label = label'
            then (fieldt', ext)
            else let val (fieldt, ext) = reorderRow expr label tail ext
                 in (fieldt, TC.OutputType (FType.RowExt (pos, {field = (label', fieldt'), ext = ext})))
                 end
         | t => raise Fail ("unimplemented at " ^ Pos.toString (TC.Expr.pos expr))

    and subUvs scope expr (uv: TC.uv, uv': TC.uv): coercion =
        case (TypeVars.uvGet uv, TypeVars.uvGet uv')
        of (Either.Left uv, Either.Left uv') =>
            if TC.uvInScope (scope, uv)
            then if TC.uvInScope (scope, uv')
                 then if TypeVars.uvEq (uv, uv')
                      then NONE
                      else ( TC.uvMerge (uv, uv'); NONE )
                 else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv'))
            else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv'))
         | (Either.Left uv, Either.Right t) => ( assign scope (Sub, uv, t); NONE )
         | (Either.Right t, Either.Left uv) => ( assign scope (Super, uv, t); NONE )
         | (Either.Right t, Either.Right t') => subType scope expr (t, t')

    and subUv scope expr uv superTyp = case TypeVars.uvGet uv
                                       of Either.Left uv => (assign scope (Sub, uv, superTyp); NONE)
                                        | Either.Right t => subType scope expr (t, superTyp)

    and superUv scope expr uv subTyp = case TypeVars.uvGet uv
                                       of Either.Left uv => (assign scope (Super, uv, subTyp); NONE)
                                        | Either.Right t => subType scope expr (subTyp, t)
end

