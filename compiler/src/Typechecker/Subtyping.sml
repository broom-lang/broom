structure Subtyping :> sig
    type effect = FlexFAst.Type.effect 

    type coercer = (FlexFAst.Term.expr -> FlexFAst.Term.expr) option
   
    val applyCoercion: coercer -> FlexFAst.Term.expr -> FlexFAst.Term.expr
    val subEffect: Pos.span -> effect * effect -> unit
    val joinEffs : effect * effect -> effect
    val subType: TypecheckingEnv.t -> Pos.span -> FlexFAst.Type.concr * FlexFAst.Type.concr -> coercer
    val unify: TypecheckingEnv.t -> Pos.span -> FlexFAst.Type.concr * FlexFAst.Type.concr -> coercer
end = struct
    val op|> = Fn.|>
    datatype either = datatype Either.t
    structure Uv = TypeVars.Uv
    structure Path = TypeVars.Path
    datatype explicitness = datatype Cst.explicitness
    datatype effect = datatype FType.effect
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

(* # Utils *)

    fun idInScope env id = isSome (Env.findType env id)

    (* FIXME: Check kinds and smallness/monotype *)
    fun uvSet env (uv, t) =
        ( Uv.set Concr.tryToUv Scope.Id.compare (Env.hasScope env) (uv, t)
        ; NONE )

    (* FIXME: Check kinds and smallness/monotype *)
    fun pathSet env =
        Path.set (Name.fromString o Concr.toString) (* HACK *)
                 (Env.hasScope env)

    (* \forall a... . T --> [(\hat{a}/a)...]T and push \hat{a}... to env *)
    fun instantiate env (params, body) f =
        let val env = Env.pushScope env (Scope.Marker (Scope.Id.fresh ()))
            val args = Vector.map (fn _ => SVar (UVar (Env.freshUv env)))
                                  params
            val mapping = (params, args)
                        |> Vector.zipWith (fn ({var, kind = _}, arg) => (var, arg))
                        |> Id.SortedMap.fromVector
            val body = Concr.substitute (Env.hasScope env) mapping body
        in f (env, args, body)
        end

    (* \forall a... . T --> T and push a... to env *)
    fun skolemize env (params, body) f =
        let val scopeId = Scope.Id.fresh ()
            val params' = Vector.map (fn {kind, var = _} => {var = Id.fresh (), kind}) params
            val env = Env.pushScope env (Scope.ForAllScope (scopeId, Bindings.Type.fromDefs params'))
            val mapping = (params, params')
                        |> Vector.zipWith (fn ({var, ...}, def') => (var, UseT def'))
                        |> Id.SortedMap.fromVector
            val body = Concr.substitute (Env.hasScope env) mapping body
        in f (env, params', body)
        end

(* # Coercions *)
(* TODO: Replace this premature optimization with shrinker pass. *)

    type coercer = (FTerm.expr -> FTerm.expr) option
    type field_coercer = (Name.t * concr) * (FTerm.expr -> FTerm.expr) * concr

    fun applyCoercion (coerce: coercer) expr =
        case coerce
        of SOME f => f expr
         | NONE => expr

    fun fnCoercion coerceDomain coerceCodomain
                   ((_, {domain = _, codomain}), (eff', {domain = domain', codomain = _})) callee =
        let val pos = FTerm.exprPos callee
            val param = {pos, id = DefId.fresh (), var = Name.fresh (), typ = domain'}
            val arg = applyCoercion coerceDomain (FTerm.Use (pos, param))
            val body = applyCoercion coerceCodomain (FTerm.App (pos, codomain, {callee, arg}))
        in FTerm.Fn (pos, param, Explicit eff', body)
        end

(* # Unification/Subtyping Generification Support *)
(* TODO: Remove this premature abstraction *)

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

(* # Effects *)

    fun joinEffs (Pure, Pure) = Pure
      | joinEffs (Pure, Impure) = Impure
      | joinEffs (Impure, Pure) = Impure
      | joinEffs (Impure, Impure) = Impure

(* # Subtyping and Unification *)

    fun unify env currPos (typs as (l, r)) =
        coercion env currPos typs
        handle TypeError cause =>
                ( Env.error env (NonUnifiable (currPos, concr l, concr r, SOME cause))
                ; SOME (fn expr =>
                            let val pos = FTerm.exprPos expr
                                val def = {pos, id = DefId.fresh (), var = Name.fresh (), typ = r}
                            in FTerm.Let ( FTerm.exprPos expr
                                         , #[FTerm.Val (pos, def, expr)]
                                         , FTerm.Use (pos, def) )
                            end) )

    and coercion (env: Env.t) currPos: concr * concr -> coercer =
        fn (ForAll universal, ForAll universal') => raise Fail "unimplemented"
         | (sub, Arrow (Implicit, {domain, codomain})) =>
            let val def = {pos = currPos, id = DefId.fresh (), var = Name.fresh (), typ = domain}
                val coerceCodomain = coercion env currPos (sub, codomain)
            in SOME (fn expr => FTerm.Fn (currPos, def, Implicit, applyCoercion coerceCodomain expr))
            end
         | (Arrow (Implicit, {domain, codomain}), super) =>
            (* FIXME: coercer from `codomain` <: `super` *)
            (case domain
             of FType.Type domain =>
                 let val arg = FTerm.Type (currPos, domain)
                 in SOME (fn expr => FTerm.App (currPos, codomain, {callee = expr, arg}))
                 end
              | _ => raise Fail "implicit parameter not of type `type`")
         | (Arrow (Explicit eff, arr), Arrow (Explicit eff', arr')) =>
            arrowCoercion Unify env currPos ((eff, arr), (eff', arr'))
         | (sub as Record row, super as Record row') =>
            recordCoercion Unify env currPos (sub, super) (row, row')
         | (sub as RowExt _, super as RowExt _) =>
           ( rowCoercion Unify env currPos (sub, super)
           ; NONE ) (* No values of row type exist => coercer unnecessary *)
         | (EmptyRow, EmptyRow) => NONE
         | (sub as Prim p, super as Prim p') =>
            primCoercion Unify currPos (p, p') (sub, super)
         | (Type (Exists (#[], t)), Type (sup as Exists (#[], t'))) =>
            ( coercion env currPos (t, t')
            ; SOME (fn _ => FTerm.Type (currPos, sup)))
         | (App {callee = SVar (Path path), args}, super) =>
            pathCoercion Unify Up env currPos (path, args) super
         | (sub, App {callee = SVar (Path path), args}) =>
            pathCoercion Unify Down env currPos (path, args) sub
         | (App {callee, args}, App {callee = callee', args = args'}) =>
            ( ignore (coercion env currPos (callee, callee'))
            ; Vector.app (ignore o coercion env currPos) (Vector.zip (args, args'))
            ; NONE )
         | (sub as CallTFn call, super as CallTFn call') =>
            tFnAppCoercion Unify env currPos (call, call') (sub, super)
         | (sub as UseT {var, ...}, super as UseT {var = var', ...}) =>
            (* TODO: Go back to using `OVar` => this becomes `raise Fail "unreachable" *)
            if var = var'
            then if idInScope env var
                 then NONE
                 else raise TypeError (OutsideScope (currPos, Name.fromString ("g__" ^ Id.toString var)))
            else raise TypeError (error Unify (currPos, concr sub, concr super, NONE))
         | (SVar (UVar uv), super as SVar (UVar uv')) =>
            uvsCoercion Unify env currPos super (uv, uv')
         | (SVar (UVar uv), super) => uvCoercion env currPos (direct Up Unify) uv super
         | (sub, SVar (UVar uv)) => uvCoercion env currPos (direct Down Unify) uv sub
         | (SVar (Path path), super) => pathCoercion Unify Up env currPos (path, #[]) super
         | (sub, SVar (Path path)) => pathCoercion Unify Down env currPos (path, #[]) sub
         | (sub, super) => raise TypeError (NonSubType (currPos, concr sub, concr super, NONE))

    (* Check that `typ` <: `superTyp` and return the coercer if any. *)
    and subType env currPos (typs as (sub, super)) =
        coercer env currPos typs
        handle TypeError cause =>
                ( Env.error env (NonSubType (currPos, concr sub, concr super, SOME cause))
                ; SOME (fn expr =>
                            let val pos = FTerm.exprPos expr
                                val def = {pos, id = DefId.fresh (), var = Name.fresh (), typ = super}
                            in FTerm.Let ( FTerm.exprPos expr
                                         , #[FTerm.Val (pos, def, expr)]
                                         , FTerm.Use (pos, def) )
                            end) )

    and coercer (env: Env.t) currPos: concr * concr -> coercer =
        fn (sub, super as ForAll universal) =>
            skolemize env universal (fn (env, params, body) =>
                Option.map (fn coerce => fn expr => FTerm.TFn (currPos, params, coerce expr))
                           (coercer env currPos (sub, body))
            )
         | (sub as ForAll universal, super) =>
            instantiate env universal (fn (env, args, body) =>
                Option.map (fn coerce => fn expr => coerce (FTerm.TApp (currPos, body, {callee = expr, args})))
                           (coercer env currPos (body, super))
            )
         | (sub, Arrow (Implicit, {domain, codomain})) =>
            let val def = {pos = currPos, id = DefId.fresh (), var = Name.fresh (), typ = domain}
                val coerceCodomain = coercer env currPos (sub, codomain)
            in SOME (fn expr => FTerm.Fn (currPos, def, Implicit, applyCoercion coerceCodomain expr))
            end
         | (Arrow (Implicit, {domain, codomain}), super) =>
            (* FIXME: coercer from `codomain` <: `super` *)
            (case domain
             of FType.Type domain =>
                 let val arg = FTerm.Type (currPos, domain)
                 in SOME (fn expr => FTerm.App (currPos, codomain, {callee = expr, arg}))
                 end
              | _ => raise Fail "implicit parameter not of type `type`")
         | (Arrow (Explicit eff, arr), Arrow (Explicit eff', arr')) =>
            arrowCoercion (Coerce ()) env currPos ((eff, arr), (eff', arr'))
         | (sub as Record row, super as Record row') =>
            recordCoercion (Coerce ()) env currPos (sub, super) (row, row')
         | (sub as RowExt _, super as RowExt _) =>
           ( rowCoercion (Coerce ()) env currPos (sub, super)
           ; NONE ) (* No values of row type exist => coercer unnecessary *)
         | (EmptyRow, EmptyRow) => NONE
         | (sub as Prim p, super as Prim p') =>
            primCoercion (Coerce ()) currPos (p, p') (sub, super)
         | (Type (Exists (#[], t)), Type (sup as Exists (#[], t'))) =>
            ( coercion env currPos (t, t')
            ; SOME (fn _ => FTerm.Type (currPos, sup)))
         | (App {callee = SVar (Path path), args}, super) =>
            pathCoercion (Coerce ()) Up env currPos (path, args) super
         | (sub, App {callee = SVar (Path path), args}) =>
            pathCoercion (Coerce ()) Down env currPos (path, args) sub
         | (App {callee, args}, App {callee = callee', args = args'}) =>
            ( ignore (coercer env currPos (callee, callee'))
            ; Vector.app (ignore o coercer env currPos) (Vector.zip (args, args'))
            ; NONE )
         | (sub as CallTFn call, super as CallTFn call') =>
            tFnAppCoercion (Coerce ()) env currPos (call, call') (sub, super)
         | (sub as UseT {var, ...}, super as UseT {var = var', ...}) =>
            (* TODO: Go back to using `OVar` => this becomes `raise Fail "unreachable" *)
            if var = var'
            then if idInScope env var
                 then NONE
                 else raise TypeError (OutsideScope (currPos, Name.fromString ("g__" ^ Id.toString var)))
            else raise TypeError (error (Coerce ()) (currPos, concr sub, concr super, NONE))
         | (SVar (UVar uv), super as SVar (UVar uv')) =>
            uvsCoercion (Coerce ()) env currPos super (uv, uv')
         | (SVar (UVar uv), super) => uvCoercion env currPos (direct Up (Coerce ())) uv super
         | (sub, SVar (UVar uv)) => uvCoercion env currPos (direct Down (Coerce ())) uv sub
         | (SVar (Path path), super) => pathCoercion (Coerce ()) Up env currPos (path, #[]) super
         | (sub, SVar (Path path)) => pathCoercion (Coerce ()) Down env currPos (path, #[]) sub
         | (sub, super) => raise TypeError (NonSubType (currPos, concr sub, concr super, NONE))

    and arrowCoercion intent env currPos
                      (arrows as ((eff, {domain, codomain}), (eff', {domain = domain', codomain = codomain'}))) =
        let do eqOrSubEffect intent currPos (eff, eff')
            val coerceDomain = coercer env currPos (domain', domain)
            val coerceCodomain = coercer env currPos (codomain, codomain')
        in if isSome coerceDomain orelse isSome coerceCodomain
           then SOME (fnCoercion coerceDomain coerceCodomain arrows)
           else NONE
        end

    and eqOrSubEffect intent currPos effs =
        case intent
        of Coerce () => (case effs
                         of (Pure, Pure) => ()
                          | (Pure, Impure) => ()
                          | (Impure, Pure) => raise Fail "Impure is not a subtype of Pure"
                          | (Impure, Impure) => ())
         | Unify => if op= effs
                    then ()
                    else raise Fail "Nonequal effects"

    and subEffect pos = eqOrSubEffect (Coerce ()) pos

    and recordCoercion intent env currPos (t, t') (row, row') =
        case rowCoercion intent env currPos (row, row')
        of [] => NONE
         | fieldCoercions =>
            SOME (fn expr =>
                      let val tmpDef = {pos = currPos, id = DefId.fresh (), var = Name.fresh (), typ = t}
                          val tmpUse = FTerm.Use (currPos, tmpDef)
                          fun emitField ((label, origFieldt), coerceField, _) =
                              (label, coerceField (FTerm.Field (currPos, origFieldt, tmpUse, label)))
                      in FTerm.Let ( currPos
                                   , #[FTerm.Val (currPos, tmpDef, expr)]
                                   , List.foldl (fn (fieldCoercion as (_, _, row'), base) =>
                                                     let val typ' = FType.Record row'
                                                     in FTerm.Where (currPos, typ', {base, field = emitField fieldCoercion})
                                                     end)
                                                tmpUse fieldCoercions )
                      end)

    and rowCoercion intent env currPos (rows: concr * concr): field_coercer list =
        let val rec subExts =
                fn (row, row' as RowExt {base = base', field = (label, fieldt')}) =>
                    let val {base, fieldt} = reorderRow currPos label (FType.rowExtBase base') row
                        val coerceField = coercer env currPos (fieldt, fieldt')
                        val coerceExt = subExts (base, base')
                    in case coerceField
                       of SOME coerceField => ((label, fieldt), coerceField, row') :: coerceExt
                        | NONE => coerceExt
                    end
                 | rows => (coercer env currPos rows; [])
        in subExts rows
        end

    and reorderRow currPos label (tail: concr): concr -> {base: concr, fieldt: concr} =
        fn RowExt {base, field = (label', fieldt')} =>
            if label = label'
            then {base, fieldt = fieldt'}
            else let val {base, fieldt} = reorderRow currPos label tail base
                 in {base = RowExt {base, field = (label', fieldt')}, fieldt}
                 end
         (* FIXME: `t` is actually row tail, not the type of `expr`. *)
         | t => raise TypeError (MissingField (currPos, t, label))

    and primCoercion intent currPos (p, p') (sub, super) =
        if p = p'
        then NONE
        else raise TypeError (error intent (currPos, concr sub, concr super, NONE))

    and tFnAppCoercion intent env currPos ((callee, args), (callee', args')) (t, t') =
        if callee = callee'
        then ( Vector.app (ignore o coercion env currPos) (Vector.zip (args, args'))
             ; Vector.app (ignore o coercion env currPos) (Vector.zip (args', args))
             ; NONE ) (* Since both callee and args have to unify, coercer is always no-op. *)
        else raise TypeError (error intent (currPos, concr t, concr t', NONE))

    and pathCoercion intent y env currPos (path, args) t =
        case Path.get (Env.hasScope env) path
        of Left (face, NONE) => (* Impl not visible => <:/~ face: *)
            let val face = App {callee = face, args}
            in coercion env currPos (case y
                                     of Up => (face , t)
                                      | Down => (t, face))
            end
         | Left (face, SOME coercionDef) => (* Impl visible and unset => define: *)
            (* FIXME: enforce predicativity: *)
            if Concr.pathOccurs path t
            then raise TypeError (Occurs (currPos, face, concr t))
            else let val params = Vector.map (fn UseT def => def) args
                     val resT = case y
                                of Up => t
                                 | Down => (case args (* HACK *)
                                            of #[] => face
                                             | _ => FType.App {callee = face, args})
                 in pathSet env (path, (params, t))
                  ; SOME (makePathCoercion y resT coercionDef args)
                 end
         | Right ((_, typ), coercionDef) => (* Impl visible and set => <:/~ impl and wrap/unwrap: *)
            let val resT = case y
                           of Up => t
                            | Down => (case args (* HACK *)
                                       of #[] => Path.face path
                                        | _ => FType.App {callee = Path.face path, args})
                val coerceToImpl = coercion env currPos (case y
                                                                of Up => (typ, t)
                                                                 | Down => (t, typ))
                val coerceToPath = makePathCoercion y resT coercionDef args
            in case coerceToImpl
               of SOME coerceToImpl => SOME (coerceToPath o coerceToImpl)
                | NONE => SOME coerceToPath
            end

    and makePathCoercion y t coercionDef args =
        case y
        of Up => (fn expr => FTerm.Cast (FTerm.exprPos expr, t, expr, AppCo {callee = UseCo coercionDef, args}))
         | Down => (fn expr => FTerm.Cast (FTerm.exprPos expr, t, expr, Symm (AppCo {callee = UseCo coercionDef, args})))

    and uvsCoercion intent env currPos superTyp (uv, uv') =
        case (Uv.get uv, Uv.get uv')
        of (Left uv, Left _) =>
            (uvSet env (uv, superTyp); NONE) (* Call `uvSet` directly to skip occurs check. *)
         | (Left uv, Right t) => assign env currPos (Coerce Up, uv, t)
         | (Right t, Left uv) => assign env currPos (Coerce Down, uv, t)
         | (Right t, Right t') => coercer env currPos (t, t')

    and uvCoercion env currPos intent uv t =
        case Uv.get uv
        of Left uv => assign env currPos (intent, uv, t)
         | Right t' =>
            (case intent
             of Coerce Up => coercer env currPos (t', t)
              | Coerce Down => coercer env currPos (t, t')
              | Unify => coercion env currPos (t, t'))

(* # Unification Variable Assignment *)

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
    and assign (env: Env.t) currPos (y, uv: concr TypeVars.uv, t: concr): coercer =
        if Concr.occurs (Env.hasScope env) uv t
        then raise TypeError (Occurs (currPos, SVar (UVar uv), concr t))
        else doAssign env currPos y (uv, t)

    and doAssign (env: Env.t) currPos y (uv, t: concr): coercer =
        case t
        of ForAll args => doAssignUniversal env currPos y uv args
         | Arrow (Explicit eff, domains) => doAssignArrow env y uv currPos eff domains
         | RowExt _ | EmptyRow | Record _ | CallTFn _ | Prim _ | Type _ => uvSet env (uv, t)
         | UseT {var, ...} => 
            ( uvSet env (uv, t)
            ; if idInScope env var
              then NONE
              else raise TypeError (OutsideScope (currPos, Name.fromString ("g__" ^ Id.toString var))) )
         | SVar (OVar ov) =>
            ( uvSet env (uv, t)
            ; if Env.hasScope env (TypeVars.Ov.scope ov)
              then NONE
              else raise TypeError (OutsideScope (currPos, TypeVars.Ov.name ov)) )
         | SVar (UVar uv') =>
            (case Uv.get uv'
             of Left _ => uvSet env (uv, t)
              | Right t => uvSet env (uv, t))
         | SVar (Path _) => uvSet env (uv, t)

    and doAssignUniversal env currPos y uv (universal as (_, _)) =
        case y
        of Coerce Up =>
            skolemize env universal (fn (env, params, body) =>
                Option.map (fn coerce => fn expr => FTerm.TFn (currPos, params, coerce expr))
                           (doAssign env currPos y (uv, body))
            )
         | Coerce Down =>
            instantiate env universal (fn (env, args, body) =>
                Option.map (fn coerce => fn callee => coerce (FTerm.TApp (currPos, body, {callee, args})))
                           (doAssign env currPos y (uv, body))
            )

    and doAssignArrow (env: Env.t) y uv pos eff (arrow as {domain, codomain}) =
        let val domainUv = TypeVars.Uv.freshSibling uv
            val codomainUv = TypeVars.Uv.freshSibling uv
            val arrow' = { domain = SVar (UVar domainUv)
                         , codomain = SVar (UVar codomainUv)}
            val t' = Arrow (Explicit eff, arrow')
            do ignore (uvSet env (uv, t'))
            val coerceDomain = assign env pos (contra y, domainUv, domain) (* contravariance *)
            val coerceCodomain = assign env pos (y, codomainUv, codomain)
        in if isSome coerceDomain orelse isSome coerceCodomain
           then let val arrows = case y
                                 of Coerce Up => ((eff, arrow'), (eff, arrow))
                                  | Coerce Down => ((eff, arrow), (eff, arrow'))
                in SOME (fnCoercion coerceDomain coerceCodomain arrows)
                end
           else NONE
        end
end

