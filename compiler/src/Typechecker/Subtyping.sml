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

    fun uvSet env =
        Uv.set Concr.tryToUv Scope.Id.compare (Env.hasScope env)

    fun pathSet env =
        Path.set (Name.fromString o Concr.toString) (* HACK *)
                 (Env.hasScope env)

    type coercion = (FTerm.expr -> FTerm.expr) option
    type field_coercion = Name.t * concr * (FTerm.expr -> FTerm.expr)

    fun applyCoercion (coerce: coercion) expr =
        case coerce
        of SOME f => f expr
         | NONE => expr

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
    fun assign (env: Env.t) (y, uv: (Scope.Id.t, concr) TypeVars.uv, t: concr): unit =
        if Concr.occurs (Env.hasScope env) uv t
        then raise TypeError (Occurs (SVar (Concr.pos t, UVar uv), concr t))
        else doAssign env y (uv, t)

    and doAssign (env: Env.t) y (uv, t: concr) =
        case t
        of Arrow (pos, domains) => doAssignArrow env y uv pos domains
         | RowExt _ => uvSet env (uv, t) (* FIXME: row kind check, t smallness check *)
         | EmptyRow _ => uvSet env (uv, t) (* FIXME: Check that uv is of row kind. *)
         | Prim _ => uvSet env (uv, t)
         | UseT (_, {var, ...}) => 
            if idInScope env var
            then uvSet env (uv, t)
            else raise Fail ("Opaque type out of scope: g__" ^ Id.toString var)
         | SVar (_, UVar uv') =>
            (case Uv.get uv'
             of Left uv' => uvSet env (uv, t)
              | Right t => uvSet env (uv, t))
         | SVar (_, Path _) => uvSet env (uv, t)

    and doAssignArrow (env: Env.t) y uv pos {domain, codomain} =
        let val domainUv = Env.freshUv env Predicative
            val codomainUv = Env.freshUv env Predicative
            val t' = Arrow (pos, { domain = SVar (pos, UVar domainUv)
                                       , codomain = SVar (pos, UVar codomainUv)})
        in uvSet env (uv, t')
         ; assign env (flipY y, domainUv, domain) (* contravariance *)
         ; assign env (y, codomainUv, codomain)
        end

    (* Check that `typ` <: `superTyp` and return the coercion if any. *)
    fun subType (env: Env.t) currPos (typ: concr, superTyp: concr): coercion =
        case (typ, superTyp)
        of (_, ForAll (_, params, body)) =>
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
                          (subType env currPos (typ, body))
            end
         | (ForAll (_, params, body), _) =>
           let val env = Env.pushScope env (Scope.Marker (Scope.Id.fresh ()))
               val args = Vector.map (fn _ => SVar (currPos, UVar (Env.freshUv env Predicative)))
                                     params
               val mapping =
                   Vector.foldl (fn (({var, ...}, arg), mapping) => Id.SortedMap.insert (mapping, var, arg))
                                Id.SortedMap.empty
                                (Vector.zip (params, args))
               val body = Concr.substitute (Env.hasScope env) mapping body
           in Option.map (fn coerce => fn expr => coerce (FTerm.TApp (currPos, body, {callee = expr, args})))
                         (subType env currPos (body, superTyp))
           end
         | (Arrow (_, arr), Arrow (_, arr')) => subArrows env currPos (arr, arr')
         | (Record (_, row), Record (_, row')) => 
            (case subRows env currPos (row, row')
             of [] => NONE
              | fieldCoercions =>
                 SOME (fn expr =>
                           let val tmpName = Name.fresh ()
                               val tmpDef = {var = tmpName, typ}
                               val tmpUse = FTerm.Use (currPos, tmpDef)
                               fun emitField (label, fieldt, coerceField) =
                                   (label, coerceField (FTerm.Field (currPos, fieldt, tmpUse, label)))
                           in FTerm.Let ( currPos, #[FTerm.Val (currPos, tmpDef, expr)]
                                        , FTerm.Override ( currPos
                                                         , superTyp
                                                         , Vector.map emitField (Vector.fromList fieldCoercions)
                                                         , tmpUse ) )
                           end))
         | (RowExt _, RowExt _) =>
           ( subRows env currPos (typ, superTyp)
           ; NONE ) (* No values of row type exist => coercion unnecessary *)
         | (EmptyRow _, EmptyRow _) => NONE
         | (Prim (_, pl), Prim (_, pr)) =>
            if pl = pr
            then NONE
            else raise Fail "<:"
         | (Type (pos, Exists (_, #[], t)), Type (_, sup as Exists (_, #[], t'))) =>
            (* TODO: Actual existentials (with params). *)
            (* TODO: Replace <: + :> with plain unification: *)
            ( subType env currPos (t, t')
            ; subType env currPos (t', t)
            ; SOME (fn _ => FTerm.Type (pos, sup)))
         | (CallTFn _, CallTFn _) => raise Fail "unimplemented"
         | (UseT (_, {var, ...}), UseT (_, {var = var', ...})) =>
            if var = var'
            then if idInScope env var
                 then NONE
                 else raise Fail ("Opaque type out of scope: " ^ Concr.toString superTyp)
            else raise TypeError (NonSubType (currPos, concr typ, concr superTyp))
         | (SVar (_, UVar uv), SVar (_, UVar uv')) =>
            (case (Uv.get uv, Uv.get uv')
             of (Left uv, Left _) =>
                 (uvSet env (uv, superTyp); NONE) (* Call `uvSet` directly to skip occurs check. *)
              | (Left uv, Right t) => (assign env (Sub, uv, t); NONE)
              | (Right t, Left uv) => (assign env (Super, uv, t); NONE)
              | (Right t, Right t') => subType env currPos (t, t'))
         | (SVar (_, UVar uv), _) => subUv env currPos uv superTyp
         | (_, SVar (_, UVar uv)) => superUv env currPos uv typ
         | (_, SVar (_, Path path)) => suberPath env currPos Super path typ
         | (SVar (_, Path path), _) => suberPath env currPos Sub path superTyp
         | _ => raise TypeError (NonSubType (currPos, concr typ, concr superTyp))

    and subArrows env currPos ({domain, codomain}, {domain = domain', codomain = codomain'}) =
        let val coerceDomain = subType env currPos (domain', domain)
            val coerceCodomain = subType env currPos (codomain, codomain')
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

    and subUv env currPos uv superTyp = case Uv.get uv
                                        of Left uv => (assign env (Sub, uv, superTyp); NONE)
                                         | Right t => subType env currPos (t, superTyp)

    and superUv env currPos uv subTyp = case Uv.get uv
                                        of Left uv => (assign env (Super, uv, subTyp); NONE)
                                         | Right t => subType env currPos (subTyp, t)

    and suberPath env currPos y path t =
        case Path.get (Env.hasScope env) path
        of Left (face, NONE) => subType env currPos (case y
                                                     of Sub => (face, t)
                                                      | Super => (t, face))
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
            in SOME (pathCoercion y resT coercionDef)
            end

    and pathCoercion y t coercionDef =
        case y
        of Sub => (fn expr => FTerm.Cast (FTerm.exprPos expr, t, expr, UseCo coercionDef))
         | Super => (fn expr => FTerm.Cast (FTerm.exprPos expr, t, expr, Symm (UseCo coercionDef)))
end

