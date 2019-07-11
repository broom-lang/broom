structure Subtyping :> sig
    type coercion = (FlexFAst.Term.expr -> FlexFAst.Term.expr) option
   
    val applyCoercion: coercion -> FlexFAst.Term.expr -> FlexFAst.Term.expr
    val subType: TypecheckingEnv.t -> Pos.t -> FlexFAst.Type.concr * FlexFAst.Type.concr -> coercion
end = struct
    datatype either = datatype Either.t
    structure Uv = TypeVars.Uv
    structure Path = TypeVars.Path
    datatype predicativity = datatype TypeVars.predicativity
    structure FAst = FlexFAst
    structure FType = FAst.Type
    structure Id = FType.Id
    structure Concr = FType.Concr
    datatype abs' = datatype FAst.Type.abs'
    datatype concr' = datatype FAst.Type.concr'
    type concr = FType.concr
    datatype sv = datatype FType.sv
    datatype co' = datatype FAst.Type.co'
    val concr = FType.Abs.concr
    structure FTerm = FAst.Term
    structure Env = TypecheckingEnv
    structure Scope = Env.Scope
    open TypeError

    fun idInScope env id = isSome (Env.findType env id)

    (* FIXME: Check kinds and smallness/monotype *)
    fun uvSet env (uv, t) =
        ( Uv.set Concr.tryToUv Scope.Id.compare (Env.hasScope env) (uv, t)
        ; NONE )

    (* FIXME: Check kinds and smallness/monotype *)
    fun pathSet env =
        Path.set (Name.fromString o Concr.toString) (* HACK *)
                 (Env.hasScope env)

    type coercion = (FTerm.expr -> FTerm.expr) option
    type field_coercion = Name.t * concr * (FTerm.expr -> FTerm.expr)

    fun applyCoercion (coerce: coercion) expr =
        case coerce
        of SOME f => f expr
         | NONE => expr

    fun fnCoercion coerceDomain coerceCodomain ({domain, codomain}, {domain = domain', codomain = codomain'}) callee =
        let val pos = FTerm.exprPos callee
            val param = {var = Name.fresh (), typ = domain'}
            val arg = applyCoercion coerceDomain (FTerm.Use (pos, param))
            val body = applyCoercion coerceCodomain (FTerm.App (pos, codomain, {callee, arg}))
        in FTerm.Fn (pos, param, body)
        end

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
    fun assign (env: Env.t) (y, uv: (Scope.Id.t, concr) TypeVars.uv, t: concr): coercion =
        if Concr.occurs (Env.hasScope env) uv t
        then raise TypeError (Occurs (SVar (Concr.pos t, UVar uv), concr t))
        else doAssign env y (uv, t)

    and doAssign (env: Env.t) y (uv, t: concr): coercion =
        case t
        of ForAll args => doAssignUniversal env y uv args
         | Arrow (pos, domains) => doAssignArrow env y uv pos domains
         | RowExt _ | EmptyRow _ | Record _ | CallTFn _ | Prim _ | Type _ => uvSet env (uv, t)
         | UseT (_, {var, ...}) => 
            if idInScope env var
            then uvSet env (uv, t)
            else raise Fail ("Opaque type out of scope: g__" ^ Id.toString var)
         | SVar (_, UVar uv') =>
            (case Uv.get uv'
             of Left uv' => uvSet env (uv, t)
              | Right t => uvSet env (uv, t))
         | SVar (_, Path _) => uvSet env (uv, t)

    and doAssignUniversal env y uv (pos, params, body) =
        case y
        of Sub =>
            let val params' = Vector.map (fn {kind, ...} => {var = Id.fresh (), kind}) params
                val env = Vector.foldl (fn (def, env) =>
                                            Env.pushScope env (Scope.ForAllScope (Scope.Id.fresh (), def)))
                                       env params'
                val mapping =
                    Vector.foldl (fn (({var, ...}, def'), mapping) =>
                                      Id.SortedMap.insert (mapping, var, UseT (pos, def')))
                                 Id.SortedMap.empty
                                 (Vector.zip (params, params'))
                val body = Concr.substitute (Env.hasScope env) mapping body
            in Option.map (fn coerce => fn expr => FTerm.TFn (pos, params', coerce expr))
                          (doAssign env y (uv, body))
            end
         | Super =>
            let val env = Env.pushScope env (Scope.Marker (Scope.Id.fresh ()))
                val args = Vector.map (fn _ => SVar (pos, UVar (Env.freshUv env Predicative)))
                                      params
                val mapping =
                    Vector.foldl (fn (({var, ...}, arg), mapping) => Id.SortedMap.insert (mapping, var, arg))
                                 Id.SortedMap.empty
                                 (Vector.zip (params, args))
                val body = Concr.substitute (Env.hasScope env) mapping body
            in Option.map (fn coerce => fn callee => coerce (FTerm.TApp (pos, body, {callee, args})))
                          (doAssign env y (uv, body))
            end

    and doAssignArrow (env: Env.t) y uv pos (arrow as {domain, codomain}) =
        let val domainUv = Env.freshUv env Predicative
            val codomainUv = Env.freshUv env Predicative
            val arrow' = { domain = SVar (pos, UVar domainUv)
                         , codomain = SVar (pos, UVar codomainUv)}
            val t' = Arrow (pos, arrow')
            do ignore (uvSet env (uv, t'))
            val coerceDomain = assign env (flipY y, domainUv, domain) (* contravariance *)
            val coerceCodomain = assign env (y, codomainUv, codomain)
        in if isSome coerceDomain orelse isSome coerceCodomain
           then let val arrows = case y
                                 of Sub => (arrow', arrow)
                                  | Super => (arrow, arrow')
                in SOME (fnCoercion coerceDomain coerceCodomain arrows)
                end
           else NONE
        end

    (* Check that `typ` <: `superTyp` and return the coercion if any. *)
    fun subType (env: Env.t) currPos (typ: concr, superTyp: concr): coercion =
        case (typ, superTyp)
        of (_, ForAll args) => suberUniversal env currPos Super args typ
         | (ForAll args, _) => suberUniversal env currPos Sub args superTyp
         | (Arrow (_, arr), Arrow (_, arr')) => subArrows env currPos (arr, arr')
         | (Record (_, row), Record (_, row')) => subRecord env currPos (typ, superTyp) (row, row')
         | (RowExt _, RowExt _) =>
           ( subRows env currPos (typ, superTyp)
           ; NONE ) (* No values of row type exist => coercion unnecessary *)
         | (EmptyRow _, EmptyRow _) => NONE
         | (Prim (_, p), Prim (_, p')) => subPrim currPos (p, p') (typ, superTyp)
         | (Type (pos, Exists (_, #[], t)), Type (_, sup as Exists (_, #[], t'))) =>
            (* TODO: Actual existentials (with params). *)
            (* TODO: Replace <: + :> with plain unification: *)
            ( subType env currPos (t, t')
            ; subType env currPos (t', t)
            ; SOME (fn _ => FTerm.Type (pos, sup)))
         | (CallTFn call, CallTFn call') => subCallTFn env currPos (call, call') (typ, superTyp)
         | (UseT (_, {var, ...}), UseT (_, {var = var', ...})) =>
            (* TODO: Go back to using `OVar` => this becomes `raise Fail "unreachable" *)
            if var = var'
            then if idInScope env var
                 then NONE
                 else raise Fail ("Opaque type out of scope: " ^ Concr.toString superTyp)
            else raise TypeError (NonSubType (currPos, concr typ, concr superTyp))
         | (SVar (_, UVar uv), SVar (_, UVar uv')) => subUvs env currPos superTyp (uv, uv')
         | (SVar (_, UVar uv), _) => suberUv env currPos Sub uv superTyp
         | (_, SVar (_, UVar uv)) => suberUv env currPos Super uv typ
         | (_, SVar (_, Path path)) => suberPath env currPos Super path typ
         | (SVar (_, Path path), _) => suberPath env currPos Sub path superTyp
         | _ => raise TypeError (NonSubType (currPos, concr typ, concr superTyp))

    and suberType env currPos y (t, t') =
        case y
        of Sub => subType env currPos (t, t')
         | Super => subType env currPos (t', t)

    and suberUniversal env currPos y (pos, params, body) t =
        case y
        of Sub =>
            let val env = Env.pushScope env (Scope.Marker (Scope.Id.fresh ()))
                val args = Vector.map (fn _ => SVar (currPos, UVar (Env.freshUv env Predicative)))
                                      params
                val mapping =
                    Vector.foldl (fn (({var, ...}, arg), mapping) => Id.SortedMap.insert (mapping, var, arg))
                                 Id.SortedMap.empty
                                 (Vector.zip (params, args))
                val body = Concr.substitute (Env.hasScope env) mapping body
            in Option.map (fn coerce => fn expr => coerce (FTerm.TApp (currPos, body, {callee = expr, args})))
                          (subType env currPos (body, t))
            end
         | Super =>
            let val params' = Vector.map (fn {kind, ...} => {var = Id.fresh (), kind}) params
                val env =
                    Vector.foldl (fn (def, env) =>
                                      Env.pushScope env (Scope.ForAllScope (Scope.Id.fresh (), def)))
                                 env params'
                val mapping =
                    Vector.foldl (fn (({var, ...}, def'), mapping) =>
                                      Id.SortedMap.insert (mapping, var, UseT (currPos, def')))
                                 Id.SortedMap.empty
                                 (Vector.zip (params, params'))
                val body = Concr.substitute (Env.hasScope env) mapping body
            in Option.map (fn coerce => fn expr => FTerm.TFn (currPos, params', coerce expr))
                          (subType env currPos (t, body))
            end

    and subArrows env currPos (arrows as ({domain, codomain}, {domain = domain', codomain = codomain'})) =
        let val coerceDomain = subType env currPos (domain', domain)
            val coerceCodomain = subType env currPos (codomain, codomain')
        in if isSome coerceDomain orelse isSome coerceCodomain
           then SOME (fnCoercion coerceDomain coerceCodomain arrows)
           else NONE
        end

    and subRecord env currPos (t, t') (row, row') =
        case subRows env currPos (row, row')
        of [] => NONE
         | fieldCoercions =>
            SOME (fn expr =>
                      let val tmpName = Name.fresh ()
                          val tmpDef = {var = tmpName, typ = t}
                          val tmpUse = FTerm.Use (currPos, tmpDef)
                          fun emitField (label, fieldt, coerceField) =
                              (label, coerceField (FTerm.Field (currPos, fieldt, tmpUse, label)))
                      in FTerm.Let ( currPos, #[FTerm.Val (currPos, tmpDef, expr)]
                                   , FTerm.Override ( currPos
                                                    , t'
                                                    , Vector.map emitField (Vector.fromList fieldCoercions)
                                                    , tmpUse ) )
                      end)

    and subRows env currPos (rows: concr * concr): field_coercion list =
        let val rec subExts =
                fn (row, RowExt (_, {field = (label, fieldt'), ext = ext'})) =>
                    let val (fieldt, ext) = reorderRow currPos label (FType.rowExtTail ext') row
                        val coerceField = subType env currPos (fieldt, fieldt')
                        val coerceExt = subExts (ext, ext')
                    in case coerceField
                       of SOME coerceField => (label, fieldt', coerceField) :: coerceExt
                        | NONE => coerceExt
                    end
                 | rows => (subType env currPos rows; [])
        in subExts rows
        end

    and reorderRow currPos label (tail: concr): concr -> concr * concr =
        fn RowExt (pos, {field = (label', fieldt'), ext = ext}) =>
            if label = label'
            then (fieldt', ext)
            else let val (fieldt, ext) = reorderRow currPos label tail ext
                 in (fieldt, RowExt (pos, {field = (label', fieldt'), ext = ext}))
                 end
         (* FIXME: `t` is actually row tail, not the type of `expr`. *)
         | t => raise TypeError (MissingField (currPos, t, label))

    and subPrim currPos (p, p') (typ, superTyp) =
        if p = p'
        then NONE
        else raise TypeError (NonSubType (currPos, concr typ, concr superTyp))

    and subCallTFn env currPos ((_, callee, args), (_, callee', args')) (t, t') =
        if callee = callee'
        then ( Vector.app (ignore o subType env currPos) (Vector.zip (args, args'))
             ; Vector.app (ignore o subType env currPos) (Vector.zip (args', args))
             ; NONE ) (* Since both callee and args have to unify, coercion is always no-op. *)
        else raise TypeError (NonSubType (currPos, concr t, concr t'))

    and subUvs env currPos superTyp (uv, uv') =
        case (Uv.get uv, Uv.get uv')
        of (Left uv, Left _) =>
            (uvSet env (uv, superTyp); NONE) (* Call `uvSet` directly to skip occurs check. *)
         | (Left uv, Right t) => assign env (Sub, uv, t)
         | (Right t, Left uv) => assign env (Super, uv, t)
         | (Right t, Right t') => subType env currPos (t, t')

    and suberUv env currPos y uv t =
        case Uv.get uv
        of Left uv => assign env (y, uv, t)
         | Right t' => suberType env currPos y (t', t)

    and suberPath env currPos y path t =
        case Path.get (Env.hasScope env) path
        of Left (face, NONE) => suberType env currPos y (face, t)
         | Left (face, SOME coercionDef) => (* FIXME: enforce predicativity: *)
            if Concr.pathOccurs path t
            then raise TypeError (Occurs (face, concr t))
            else let val resT = case y
                                of Sub => t
                                 | Super => face
                 in pathSet env (path, t)
                  ; SOME (pathCoercion y resT coercionDef)
                 end
         | Right (typ, coercionDef) =>
            let val resT = case y
                           of Sub => t
                            | Super => Path.face path
                val coerceToImpl = suberType env currPos y (typ, t)
                val coerceToPath = pathCoercion y resT coercionDef
            in case coerceToImpl
               of SOME coerceToImpl => SOME (coerceToPath o coerceToImpl)
                | NONE => SOME coerceToPath
            end

    and pathCoercion y t coercionDef =
        case y
        of Sub => (fn expr => FTerm.Cast (FTerm.exprPos expr, t, expr, UseCo coercionDef))
         | Super => (fn expr => FTerm.Cast (FTerm.exprPos expr, t, expr, Symm (UseCo coercionDef)))
end

