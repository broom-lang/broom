structure Subtyping :> sig
    val subType: TypecheckingCst.scope -> TypecheckingCst.typ * TypecheckingCst.typ
               -> (TypecheckingCst.expr ref -> unit) option
end = struct
    structure TC = TypecheckingCst
    structure FType = FAst.Type
    structure FTerm = FAst.Term
    open TypeError

    fun fexprValBindings fexpr =
        let val addBinder =
                fn (FTerm.ValueBinder ({var, typ}, value), bindings) =>
                    ( NameHashTable.insert bindings (var, { binder = {typ = ref (SOME (!typ)), value}
                                                          , shade = ref TC.White })
                    ; bindings )
            val bindings = NameHashTable.mkTable (0, Subscript)
        in FTerm.foldBinders addBinder bindings fexpr
        end

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
            val t' = FType.Arrow (pos, { domain = ref (TC.UVar (pos, domainUv))
                                       , codomain = ref (TC.UVar (pos, codomainUv))})
        in TypeVars.uvSet (uv, TC.OutputType t')
         ; assign scope (flipY y, domainUv, !domain) (* contravariance *)
         ; assign scope (y, codomainUv, !codomain)
        end

    and doAssignUv scope y (uv, uv') = case TypeVars.uvGet uv'
                                       of Either.Left uv' => TC.uvMerge (uv, uv')
                                        | Either.Right t => doAssign scope y (uv, t)

    (* Check that `typ` <: `superTyp` and return the (mutating) coercion if any. *)
    fun subType scope (typ: TC.typ, superTyp: TC.typ): (TC.expr ref -> unit) option =
        case (typ, superTyp)
        of (TC.OutputType t, TC.OutputType t') =>
            (case (t, t')
             of (FType.Arrow (_, arr), FType.Arrow (_, arr')) => subArrows scope (arr, arr')
              | (FType.Record (_, ref row), FType.Record (_, ref row')) => subType scope (row, row')
              | (FType.RowExt (_, row), FType.RowExt _) => subRowExts scope (row, superTyp)
              | (FType.EmptyRow _, FType.EmptyRow _) => NONE
              | (FType.Prim (_, pl), FType.Prim (_, pr)) =>
                 if pl = pr
                 then NONE
                 else raise Fail "<:"
              | (FType.Type (pos, tref as ref t), FType.Type (_, ref t')) =>
                 ( subType scope (t, t')
                 ; subType scope (t', t)
                 ; SOME (fn expr => expr := TC.OutputExpr (FTerm.Type (pos, tref)))))
         | (TC.UVar (_, uv), TC.UVar (_, uv')) => subUvs scope (uv, uv')
         | (TC.UVar (_, uv), _) => subUv scope uv superTyp
         | (_, TC.UVar (_, uv)) => superUv scope uv typ

    and subArrows scope ({domain, codomain}, {domain = domain', codomain = codomain'}) =
        let val coerceDomain = subType scope (!domain', !domain)
            val coerceCodomain = subType scope (!codomain, !codomain')
        in if isSome coerceDomain orelse isSome coerceCodomain
           then let val coerceDomain = getOpt (coerceDomain, fn _ => ())
                    val coerceCodomain = getOpt (coerceCodomain, fn _ => ())
                in SOME (fn expr =>
                             let val pos = TC.exprPos (!expr)
                                 val param = {var = Name.fresh (), typ = domain'}
                                 val arg = ref (TC.OutputExpr (FTerm.Use (pos, param)))
                                 val callee = ref (!expr)
                                 do coerceDomain arg
                                 val body = ref (TC.OutputExpr (FTerm.App (pos, codomain, {callee, arg})))
                                 do coerceCodomain body
                                 val expr' = FTerm.Fn (pos, param, body)
                             in expr := TC.OutputExpr expr'
                             end)
                end
           else NONE
        end

    and subRowExts scope (row as {field = (label, fieldt), ext}, row') =
        let val (fieldt', ext') = reorderRow label (!(TC.Type.rowExtTail (!ext))) row'
            val coerceField = subType scope (!fieldt, fieldt')
            val coerceExt = subType scope (!ext, ext')
        in (* FIXME: This coercion combination assumes this is a record row: *)
           SOME (fn expr =>
                     let val pos = TC.exprPos (!expr)
                         val recordTyp = TC.wrapOT (FType.Record (pos, TC.wrapOT (FType.RowExt (pos, row))))
                         val row' = {field = (label, ref fieldt'), ext = ref ext'}
                         val recordTyp' = TC.wrapOT (FType.Record (pos, TC.wrapOT (FType.RowExt (pos, row'))))
                         val recordDef = {var = Name.fresh (), typ = recordTyp}
                         val recordBind = FTerm.Val (pos, recordDef, ref (!expr))
                         val recordRef = TC.wrapOE (FTerm.Use (pos, recordDef))
                         val fieldGet = TC.wrapOE (FTerm.Field (pos, fieldt, recordRef, label))
                         do getOpt (coerceField, fn _ => ()) fieldGet
                         val fieldDef = {var = Name.freshen label, typ = ref fieldt'}
                         val fieldRedef = FTerm.Val (pos, fieldDef, fieldGet)
                         val extTyp = TC.wrapOT (FType.Record (pos, ref ext'))
                         val extGet = TC.wrapOE (FTerm.Use (pos, recordDef))
                         do getOpt (coerceExt, fn _ => ()) extGet
                         val extRedef = FTerm.Val (pos, {var = Name.fresh (), typ = extTyp}, extGet)
                         val body = TC.wrapOE (FTerm.Extend ( pos, recordTyp'
                                                            , Vector.fromList [(label, TC.wrapOE (FTerm.Use (pos, fieldDef)))]
                                                            , SOME (TC.wrapOE (FTerm.Use (pos, recordDef))) ))
                         val expr' = FTerm.Let (pos, Vector.fromList [recordBind, fieldRedef, extRedef], body)
                         val expr' = TC.ScopeExpr { parent = ref (SOME scope) (* FIXME: Children will skip this :( *)
                                                  , vals = fexprValBindings expr'
                                                  , expr = TC.wrapOE expr' }
                     in expr := expr'
                     end)
        end

    and reorderRow label (tail: TC.typ): TC.typ -> TC.typ * TC.typ =
        fn TC.OutputType (FType.RowExt (pos, {field = (label', fieldt'), ext = ref ext})) =>
            if label = label'
            then (!fieldt', ext)
            else let val (fieldt, ext) = reorderRow label tail ext
                 in (fieldt, TC.OutputType (FType.RowExt (pos, {field = (label', fieldt'), ext = ref ext})))
                 end

    and subUvs scope (uv: TC.uv, uv': TC.uv): (TC.expr ref -> unit) option =
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
         | (Either.Right t, Either.Right t') => subType scope (t, t')

    and subUv scope uv superTyp = case TypeVars.uvGet uv
                                  of Either.Left uv => (assign scope (Sub, uv, superTyp); NONE)
                                   | Either.Right t => subType scope (t, superTyp)

    and superUv scope uv subTyp = case TypeVars.uvGet uv
                                  of Either.Left uv => (assign scope (Super, uv, subTyp); NONE)
                                   | Either.Right t => subType scope (subTyp, t)
end

