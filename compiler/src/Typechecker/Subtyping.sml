structure Subtyping :> sig
    type coercion = (TypecheckingCst.sv FAst.Term.expr -> TypecheckingCst.sv FAst.Term.expr) option
   
    val applyCoercion: coercion -> TypecheckingCst.sv FAst.Term.expr -> TypecheckingCst.sv FAst.Term.expr
    val subType: TypecheckingEnv.t -> Pos.t -> TypecheckingCst.abs * TypecheckingCst.abs -> coercion
end = struct
    datatype predicativity = datatype TypeVars.predicativity
    structure TC = TypecheckingCst
    structure FType = FAst.Type
    datatype abs = datatype FType.abs
    structure FTerm = FAst.Term
    structure Env = TypecheckingEnv
    open TypeError

    fun idInScope env id = isSome (Env.findType env id)

    val uvMerge = TypeVars.uvMerge Env.Scope.Id.compare

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
    fun assign (env: Env.t) (y, uv: (Env.Scope.Id.t, TC.concr) TypeVars.uv, t: TC.abs): unit =
        if Env.uvInScope (env, uv)
        then if TC.absOccurs uv t
             then raise TypeError (Occurs (uv, t))
             else doAssign env y (uv, t)
        else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv))

    and doAssign (env: Env.t) y (uv, typ: TC.abs) =
        case typ
        of Exists _ => raise Fail "unimplemented"
         | Concr t =>
            (case t
             of FType.Arrow (pos, domains) => doAssignArrow env y uv pos domains
              | FType.RowExt _ => TypeVars.uvSet (uv, t) (* FIXME: row kind check, t smallness check *)
              | FType.EmptyRow _ => TypeVars.uvSet (uv, t) (* FIXME: Check that uv is of row kind. *)
              | FType.Prim _ => TypeVars.uvSet (uv, t)
              | FType.UseT (_, {var, ...}) => 
                 if idInScope env var
                 then TypeVars.uvSet (uv, t)
                 else raise Fail ("Opaque type out of scope: g__" ^ Id.toString var)
              | FType.SVar (_, TC.UVar uv') => doAssignUv env y (uv, uv'))

    and doAssignArrow (env: Env.t) y uv pos {domain, codomain} =
        let val domainUv = Env.freshUv env Predicative
            val codomainUv = Env.freshUv env Predicative
            val t' = FType.Arrow (pos, { domain = FType.SVar (pos, TC.UVar domainUv)
                                       , codomain = FType.SVar (pos, TC.UVar codomainUv)})
        in TypeVars.uvSet (uv, t')
         ; assign env (flipY y, domainUv, Concr domain) (* contravariance *)
         ; assign env (y, codomainUv, Concr codomain)
        end

    and doAssignUv (env: Env.t) y (uv, uv') =
        case TypeVars.uvGet uv'
        of Either.Left uv' => uvMerge (uv, uv')
         | Either.Right t => doAssign env y (uv, Concr t)

    (* Check that `typ` <: `superTyp` and return the coercion if any. *)
    fun subType (env: Env.t) currPos (typ: TC.abs, superTyp: TC.abs): coercion =
        case (typ, superTyp)
        of (Concr t, Concr t') =>
            (case (t, t')
             of (FType.ForAll _, _) => raise Fail "unimplemented"
              | (_, FType.ForAll _) => raise Fail "unimplemented"
              | (FType.Arrow (_, arr), FType.Arrow (_, arr')) => subArrows env currPos (arr, arr')
              | (FType.Record (_, row), FType.Record (_, row')) => 
                 (case subRows env currPos (row, row')
                  of [] => NONE)
              | (FType.RowExt _, FType.RowExt _) =>
                ( subRows env currPos (t, t')
                ; NONE ) (* No values of row type exist => coercion unnecessary *)
              | (FType.EmptyRow _, FType.EmptyRow _) => NONE
              | (FType.Prim (_, pl), FType.Prim (_, pr)) =>
                 if pl = pr
                 then NONE
                 else raise Fail "<:"
              | (FType.Type (pos, t), FType.Type (_, t')) =>
                 ( subType env currPos (t, t')
                 ; subType env currPos (t', t)
                 ; SOME (fn _ => FTerm.Type (pos, t)))
              | (FType.UseT (_, {var, ...}), FType.UseT (_, {var = var', ...})) =>
                 if var = var'
                 then if idInScope env var
                      then NONE
                      else raise Fail ("Opaque type out of scope: " ^ TC.Type.absToString superTyp)
                 else raise TypeError (NonSubType (currPos, typ, superTyp))
              | (FType.SVar (_, TC.UVar uv), FType.SVar (_, TC.UVar uv')) => subUvs env currPos (uv, uv')
              | (FType.SVar (_, TC.UVar uv), _) => subUv env currPos uv superTyp
              | (_, FType.SVar (_, TC.UVar uv)) => superUv env currPos uv typ
              | _ => raise Fail ("unimplemented: " ^ TC.Type.absToString typ ^ " <: "
                                 ^ TC.Type.absToString superTyp))

    and subArrows env currPos ({domain, codomain}, {domain = domain', codomain = codomain'}) =
        let val coerceDomain = subType env currPos (Concr domain', Concr domain)
            val coerceCodomain = subType env currPos (Concr codomain, Concr codomain')
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

    and subRows env currPos (rows: TC.concr * TC.concr): field_coercion list =
        let val rec subExts =
                fn (row, FType.RowExt (_, {field = (label, fieldt'), ext = ext'})) =>
                    let val (fieldt, ext) = reorderRow currPos label (FType.rowExtTail ext') row
                        val coerceField = subType env currPos (Concr fieldt, Concr fieldt')
                        val coerceExt = subExts (ext, ext')
                    in case coerceField
                       of SOME coerceField => (label, coerceField) :: coerceExt
                        | NONE => coerceExt
                    end
                 | rows => (subType env currPos (Pair.bimap Concr Concr rows); [])
        in subExts rows
        end

    and reorderRow currPos label (tail: TC.concr): TC.concr -> TC.concr * TC.concr =
        fn FType.RowExt (pos, {field = (label', fieldt'), ext = ext}) =>
            if label = label'
            then (fieldt', ext)
            else let val (fieldt, ext) = reorderRow currPos label tail ext
                 in (fieldt, FType.RowExt (pos, {field = (label', fieldt'), ext = ext}))
                 end
         (* FIXME: `t` is actually row tail, not the type of `expr`. *)
         | t => raise TypeError (MissingField (currPos, t, label))

    and subUvs env currPos (uv: TC.uv, uv': TC.uv): coercion =
        case (TypeVars.uvGet uv, TypeVars.uvGet uv')
        of (Either.Left uv, Either.Left uv') =>
            if Env.uvInScope (env, uv)
            then if Env.uvInScope (env, uv')
                 then if TypeVars.uvEq (uv, uv')
                      then NONE
                      else ( uvMerge (uv, uv'); NONE )
                 else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv'))
            else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv'))
         | (Either.Left uv, Either.Right t) => ( assign env (Sub, uv, Concr t); NONE )
         | (Either.Right t, Either.Left uv) => ( assign env (Super, uv, Concr t); NONE )
         | (Either.Right t, Either.Right t') => subType env currPos (Concr t, Concr t')

    and subUv env currPos uv superTyp = case TypeVars.uvGet uv
                                       of Either.Left uv => (assign env (Sub, uv, superTyp); NONE)
                                        | Either.Right t => subType env currPos (Concr t, superTyp)

    and superUv env currPos uv subTyp = case TypeVars.uvGet uv
                                       of Either.Left uv => (assign env (Super, uv, subTyp); NONE)
                                        | Either.Right t => subType env currPos (subTyp, Concr t)
end

