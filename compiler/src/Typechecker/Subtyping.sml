structure Subtyping :> sig
    type coercion = (FlexFAst.Term.expr -> FlexFAst.Term.expr) option
   
    val applyCoercion: coercion -> FlexFAst.Term.expr -> FlexFAst.Term.expr
    val subType: TypecheckingEnv.t -> Pos.t -> FlexFAst.Type.concr * FlexFAst.Type.concr -> coercion
    val unify: TypecheckingEnv.t -> Pos.t -> FlexFAst.Type.concr * FlexFAst.Type.concr -> coercion
end = struct
    val op|> = Fn.|>
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
    structure Bindings = Env.Bindings
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

    fun instantiate env (pos, params, body) f =
        let val env = Env.pushScope env (Scope.Marker (Scope.Id.fresh ()))
            val args = Vector.map (fn _ => SVar (pos, UVar (Env.freshUv env Predicative)))
                                  params
            val mapping = (params, args)
                        |> Vector.zipWith (fn ({var, kind = _}, arg) => (var, arg))
                        |> Id.SortedMap.fromVector
            val body = Concr.substitute (Env.hasScope env) mapping body
        in f (env, args, body)
        end

    fun skolemize env (pos, params, body) f =
        let val params' = Vector.map (fn {kind, var = _} => {var = Id.fresh (), kind}) params
            val env = Env.pushScope env (Scope.ForAllScope ( Scope.Id.fresh ()
                                                           , Bindings.Type.fromDefs params' ))
            val mapping = (params, params')
                        |> Vector.zipWith (fn ({var, ...}, def') => (var, UseT (pos, def')))
                        |> Id.SortedMap.fromVector
            val body = Concr.substitute (Env.hasScope env) mapping body
        in f (env, params', body)
        end

    type coercion = (FTerm.expr -> FTerm.expr) option
    type field_coercion = Name.t * concr * (FTerm.expr -> FTerm.expr)

    fun applyCoercion (coerce: coercion) expr =
        case coerce
        of SOME f => f expr
         | NONE => expr

    fun fnCoercion coerceDomain coerceCodomain ({domain = _, codomain}, {domain = domain', codomain = _}) callee =
        let val pos = FTerm.exprPos callee
            val param = {var = Name.fresh (), typ = domain'}
            val arg = applyCoercion coerceDomain (FTerm.Use (pos, param))
            val body = applyCoercion coerceCodomain (FTerm.App (pos, codomain, {callee, arg}))
        in FTerm.Fn (pos, param, body)
        end

    datatype 'direction intent
        = Coerce of 'direction
        | Unify

    datatype direction = Up | Down

    fun direct direction =
        fn Coerce () => Coerce direction
         | Unify => Unify

    val contra =
        fn Coerce Up => Coerce Down
         | Coerce Down => Coerce Up
         | Unify => Unify

    val error =
        fn Coerce _ => NonSubType
         | Unify => NonUnifiable

    (* Check that `typ` <: `superTyp` and return the coercion if any. *)
    fun coercion (intent: unit intent) (env: Env.t) currPos: concr * concr -> coercion =
        fn (sub as ForAll universal, super) =>
            (case intent
             of Coerce () =>
                 instantiate env universal (fn (env, args, body) =>
                     Option.map (fn coerce => fn expr => coerce (FTerm.TApp (currPos, body, {callee = expr, args})))
                                (subType env currPos (body, super))
                 )
              | Unify =>
                 (case super
                  of ForAll universal' => raise Fail "unimplemented"
                   | _ => raise TypeError (NonUnifiable (currPos, concr sub, concr super))))
         | (sub, super as ForAll universal) =>
            (case intent
             of Coerce () =>
                 skolemize env universal (fn (env, params, body) =>
                     Option.map (fn coerce => fn expr => FTerm.TFn (currPos, params, coerce expr))
                                (subType env currPos (sub, body))
                 )
              | Unify => raise TypeError (NonUnifiable (currPos, concr sub, concr super)))
         | (Arrow (_, arr), Arrow (_, arr')) => arrowCoercion intent env currPos (arr, arr')
         | (sub as Record (_, row), super as Record (_, row')) =>
            recordCoercion intent env currPos (sub, super) (row, row')
         | (sub as RowExt _, super as RowExt _) =>
           ( rowCoercion intent env currPos (sub, super)
           ; NONE ) (* No values of row type exist => coercion unnecessary *)
         | (EmptyRow _, EmptyRow _) => NONE
         | (sub as Prim (_, p), super as Prim (_, p')) =>
            primCoercion intent currPos (p, p') (sub, super)
         | (Type (pos, Exists (_, #[], t)), Type (_, sup as Exists (_, #[], t'))) =>
            ( unify env currPos (t, t')
            ; SOME (fn _ => FTerm.Type (pos, sup)))
         | (sub as CallTFn call, super as CallTFn call') =>
            tFnAppCoercion intent env currPos (call, call') (sub, super)
         | (sub as UseT (_, {var, ...}), super as UseT (_, {var = var', ...})) =>
            (* TODO: Go back to using `OVar` => this becomes `raise Fail "unreachable" *)
            if var = var'
            then if idInScope env var
                 then NONE
                 else raise Fail ("Opaque type out of scope: " ^ Concr.toString super)
            else raise TypeError (error intent (currPos, concr sub, concr super))
         | (SVar (_, UVar uv), super as SVar (_, UVar uv')) =>
            uvsCoercion intent env currPos super (uv, uv')
         | (SVar (_, UVar uv), super) => uvCoercion env currPos (direct Up intent) uv super
         | (sub, SVar (_, UVar uv)) => uvCoercion env currPos (direct Down intent) uv sub
         | (SVar (_, Path path), super) => pathCoercion intent Up env currPos path super
         | (sub, SVar (_, Path path)) => pathCoercion intent Down env currPos path sub
         | (sub, super) => raise TypeError (NonSubType (currPos, concr sub, concr super))

    and subType env = coercion (Coerce ()) env

    and unify env = coercion Unify env

    and arrowCoercion intent env currPos (arrows as ({domain, codomain}, {domain = domain', codomain = codomain'})) =
        let val coerceDomain = coercion intent env currPos (domain', domain)
            val coerceCodomain = coercion intent env currPos (codomain, codomain')
        in if isSome coerceDomain orelse isSome coerceCodomain
           then SOME (fnCoercion coerceDomain coerceCodomain arrows)
           else NONE
        end

    and recordCoercion intent env currPos (t, t') (row, row') =
        case rowCoercion intent env currPos (row, row')
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

    and rowCoercion intent env currPos (rows: concr * concr): field_coercion list =
        let val rec subExts =
                fn (row, RowExt (_, {field = (label, fieldt'), ext = ext'})) =>
                    let val (fieldt, ext) = reorderRow currPos label (FType.rowExtTail ext') row
                        val coerceField = coercion intent env currPos (fieldt, fieldt')
                        val coerceExt = subExts (ext, ext')
                    in case coerceField
                       of SOME coerceField => (label, fieldt', coerceField) :: coerceExt
                        | NONE => coerceExt
                    end
                 | rows => (coercion intent env currPos rows; [])
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

    and primCoercion intent currPos (p, p') (sub, super) =
        if p = p'
        then NONE
        else raise TypeError (error intent (currPos, concr sub, concr super))

    and tFnAppCoercion intent env currPos ((_, callee, args), (_, callee', args')) (t, t') =
        if callee = callee'
        then ( Vector.app (ignore o unify env currPos) (Vector.zip (args, args'))
             ; Vector.app (ignore o unify env currPos) (Vector.zip (args', args))
             ; NONE ) (* Since both callee and args have to unify, coercion is always no-op. *)
        else raise TypeError (error intent (currPos, concr t, concr t'))

    and pathCoercion intent y env currPos path t =
        case Path.get (Env.hasScope env) path
        of Left (face, NONE) => (* Impl not visible => <:/~ face: *)
            coercion intent env currPos (case y
                                         of Up => (face, t)
                                          | Down => (t, face))
         | Left (face, SOME coercionDef) => (* Impl visible and unset => define: *)
            (* FIXME: enforce predicativity: *)
            if Concr.pathOccurs path t
            then raise TypeError (Occurs (face, concr t))
            else let val resT = case y
                                of Up => t
                                 | Down => face
                 in pathSet env (path, t)
                  ; SOME (makePathCoercion y resT coercionDef)
                 end
         | Right (typ, coercionDef) => (* Impl visible and set => <:/~ impl and wrap/unwrap: *)
            let val resT = case y
                           of Up => t
                            | Down => Path.face path
                val coerceToImpl = coercion intent env currPos (case y
                                                                of Up => (typ, t)
                                                                 | Down => (t, typ))
                val coerceToPath = makePathCoercion y resT coercionDef
            in case coerceToImpl
               of SOME coerceToImpl => SOME (coerceToPath o coerceToImpl)
                | NONE => SOME coerceToPath
            end

    and makePathCoercion y t coercionDef =
        case y
        of Up => (fn expr => FTerm.Cast (FTerm.exprPos expr, t, expr, UseCo coercionDef))
         | Down => (fn expr => FTerm.Cast (FTerm.exprPos expr, t, expr, Symm (UseCo coercionDef)))

    and uvsCoercion intent env currPos superTyp (uv, uv') =
        case (Uv.get uv, Uv.get uv')
        of (Left uv, Left _) =>
            (uvSet env (uv, superTyp); NONE) (* Call `uvSet` directly to skip occurs check. *)
         | (Left uv, Right t) => assign env (Coerce Up, uv, t)
         | (Right t, Left uv) => assign env (Coerce Down, uv, t)
         | (Right t, Right t') => coercion intent env currPos (t, t')

    and uvCoercion env currPos intent uv t =
        case Uv.get uv
        of Left uv => assign env (intent, uv, t)
         | Right t' =>
            (case intent
             of Coerce Up => subType env currPos (t', t)
              | Coerce Down => subType env currPos (t, t')
              | Unify => unify env currPos (t, t'))

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
    and assign (env: Env.t) (y, uv: (Scope.Id.t, concr) TypeVars.uv, t: concr): coercion =
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
         | SVar (_, OVar ov) =>
            if Env.hasScope env (TypeVars.Ov.scope ov)
            then uvSet env (uv, t)
            else raise Fail ("Opaque type out of scope: " ^ Name.toString (TypeVars.Ov.name ov))
         | SVar (_, UVar uv') =>
            (case Uv.get uv'
             of Left _ => uvSet env (uv, t)
              | Right t => uvSet env (uv, t))
         | SVar (_, Path _) => uvSet env (uv, t)

    and doAssignUniversal env y uv (universal as (pos, _, _)) =
        case y
        of Coerce Up =>
            skolemize env universal (fn (env, params, body) =>
                Option.map (fn coerce => fn expr => FTerm.TFn (pos, params, coerce expr))
                           (doAssign env y (uv, body))
            )
         | Coerce Down =>
            instantiate env universal (fn (env, args, body) =>
                Option.map (fn coerce => fn callee => coerce (FTerm.TApp (pos, body, {callee, args})))
                           (doAssign env y (uv, body))
            )

    and doAssignArrow (env: Env.t) y uv pos (arrow as {domain, codomain}) =
        let val domainUv = TypeVars.Uv.freshSibling (uv, Predicative)
            val codomainUv = TypeVars.Uv.freshSibling (uv, Predicative)
            val arrow' = { domain = SVar (pos, UVar domainUv)
                         , codomain = SVar (pos, UVar codomainUv)}
            val t' = Arrow (pos, arrow')
            do ignore (uvSet env (uv, t'))
            val coerceDomain = assign env (contra y, domainUv, domain) (* contravariance *)
            val coerceCodomain = assign env (y, codomainUv, codomain)
        in if isSome coerceDomain orelse isSome coerceCodomain
           then let val arrows = case y
                                 of Coerce Up => (arrow', arrow)
                                  | Coerce Down => (arrow, arrow')
                in SOME (fnCoercion coerceDomain coerceCodomain arrows)
                end
           else NONE
        end
end

