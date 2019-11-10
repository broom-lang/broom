structure Subtyping :> sig
    type effect = FlexFAst.Type.effect

    type coercer = (FlexFAst.Term.expr -> FlexFAst.Term.expr) option
   
    val applyCoercion: coercer -> FlexFAst.Term.expr -> FlexFAst.Term.expr
    val subEffect: Pos.span -> effect * effect -> unit
    val joinEffs : effect * effect -> effect
    val subType: TypecheckingEnv.t -> Pos.span -> FlexFAst.Type.concr * FlexFAst.Type.concr -> coercer
    val unify: TypecheckingEnv.t -> Pos.span -> FlexFAst.Type.concr * FlexFAst.Type.concr -> FlexFAst.Type.co
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
    val pathOccurs = Concr.pathOccurs
    datatype concr' = datatype FAst.Type.concr'
    type concr = FType.concr
    datatype sv = datatype FType.sv
    datatype co' = datatype FAst.Type.co'
    type co = FType.co
    structure FTerm = FAst.Term
    val Cast = FTerm.Cast
    val exprPos = FTerm.exprPos
    structure Env = TypecheckingEnv
    structure Scope = Env.Scope
    structure Bindings = Env.Bindings
    val checkMonotypeKind = Kindchecker.checkMonotypeKind
    open TypeError

(* # Utils *)

    fun idInScope env id = isSome (Env.findType env id)

    fun uvSet env = Uv.set Concr.tryToUv Scope.Id.compare (Env.hasScope env)
    fun uvMerge env = Uv.merge Scope.Id.compare (Env.hasScope env)

    fun pathGet env = Path.get (Env.hasScope env)

    fun occurs env = Concr.occurs (Env.hasScope env)

    (* \forall|\exists a... . T --> [(\hat{a}/a)...]T and push \hat{a}... to env *)
    fun instantiate env (params: FType.def vector1, body) f =
        let val env = Env.pushScope env (Scope.Marker (Scope.Id.fresh ()))
            val args = Vector1.map (fn {kind, ...} => SVar (UVar (Env.freshUv env kind)))
                                   params
            val mapping = (params, args)
                        |> Vector1.zipWith (fn ({var, kind = _}, arg) => (var, arg))
                        |> Vector1.toVector
                        |> Id.SortedMap.fromVector
            val body = Concr.substitute (Env.hasScope env) mapping body
        in f (env, args, body)
        end

    (* \forall|\exists a... . T --> T and push a... to env *)
    fun skolemize env (params: FType.def vector1, body) f =
        let val scopeId = Scope.Id.fresh ()
            val params' = Vector1.map (fn {kind, var = _} => {var = Id.fresh (), kind}) params
            val env = Env.pushScope env (Scope.ForAllScope (scopeId, Bindings.Type.fromDefs params'))
            val mapping = (params, params')
                        |> Vector1.zipWith (fn ({var, ...}, def') => (var, UseT def'))
                        |> Vector1.toVector
                        |> Id.SortedMap.fromVector
            val body = Concr.substitute (Env.hasScope env) mapping body
        in f (env, params', body)
        end

    fun equiSkolemize env pos ((params, body), (params', body')) f =
        let val scopeId = Scope.Id.fresh ()
            do Vector1.zip (params, params') (* FIXME: arity errors *)
               |> Vector1.app (fn ({kind, var = _}, {kind = kind', var = _}) =>
                                   if kind = kind'
                                   then ()
                                   else raise TypeError (InequalKinds (pos, kind, kind')))
            val params'' = Vector1.map (fn {kind, var = _} => {var = Id.fresh (), kind}) params
            val env = Env.pushScope env (Scope.ForAllScope (scopeId, Bindings.Type.fromDefs params''))
            val mapping = (params, params'')
                        |> Vector1.zipWith (fn ({var, ...}, def') => (var, UseT def'))
                        |> Vector1.toVector
                        |> Id.SortedMap.fromVector
            val body = Concr.substitute (Env.hasScope env) mapping body
            val mapping' = (params', params'')
                         |> Vector1.zipWith (fn ({var, ...}, def') => (var, UseT def'))
                         |> Vector1.toVector
                         |> Id.SortedMap.fromVector
            val body' = Concr.substitute (Env.hasScope env) mapping' body'
        in f (env, params'', (body, body'))
        end
 
    fun reorderRow pos label: concr -> {base: concr, fieldt: concr} =
        fn RowExt {base, field = (label', fieldt')} =>
            if label = label'
            then {base, fieldt = fieldt'}
            else let val {base, fieldt} = reorderRow pos label base
                 in {base = RowExt {base, field = (label', fieldt')}, fieldt}
                 end
         (* FIXME: `t` is actually row tail, not the type of `expr`. *)
         | t => raise TypeError (MissingField (pos, t, label))

    fun applyType t args =
        case Vector1.fromVector args
        of SOME args => App {callee = t, args}
         | NONE => t

    fun instantiateCoercion co args =
        case Vector1.fromVector args
        of SOME args => InstCo {callee = co, args}
         | NONE => co

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

    datatype direction = Up | Down

    fun flip Up = Down
      | flip Down = Up

(* # Effects *)

    fun joinEffs (Pure, Pure) = Pure
      | joinEffs (Pure, Impure) = Impure
      | joinEffs (Impure, Pure) = Impure
      | joinEffs (Impure, Impure) = Impure

(* # Unification *)

    fun unify env pos (typs as (l, r)) =
        coercion env pos typs
        handle TypeError cause =>
                ( Env.error env (NonUnifiable (pos, l, r, SOME cause))
                ; Refl r )

    and coercion env pos (Exists existential, Exists existential') =
         equiSkolemize env pos (existential, existential') (fn (env, params, (body, body')) =>
             ExistsCo (params, coercion env pos (body, body'))
         )

      | coercion env pos (ForAll universal, ForAll universal') =
         equiSkolemize env pos (universal, universal') (fn (env, params, (body, body')) =>
             ForAllCo (params, coercion env pos (body, body'))
         )

      | coercion env pos ( Arrow (arr, {domain, codomain})
                         , Arrow (arr', {domain = domain', codomain = codomain'}) ) =
         if not (arr = arr')
         then raise Fail "arrows"
         else ArrowCo (arr, { domain = coercion env pos (domain, domain')
                            , codomain = coercion env pos (codomain, codomain') })

      | coercion env pos (Record row, Record row') = RecordCo (coercion env pos (row, row'))

      | coercion env pos (row as RowExt _, RowExt {base = base', field = (label', fieldt')}) =
         let val {base, fieldt} = reorderRow pos label' row
             val fieldCoercion = coercion env pos (fieldt, fieldt')
             val baseCoercion = coercion env pos (base, base')
         in RowExtCo { base = coercion env pos (base, base')
                     , field = (label', coercion env pos (fieldt, fieldt')) }
         end

      | coercion env pos (EmptyRow, EmptyRow) = Refl EmptyRow

      | coercion env pos (Type t, Type t') = TypeCo (coercion env pos (t, t'))

      | coercion env pos ( App {callee = SVar (Path path), args}
                         , App {callee = SVar (Path path'), args = args'} ) =
         pathsCoercion env pos ((path, Vector1.toVector args), (path', Vector1.toVector args')) 

      | coercion env pos (App {callee = SVar (Path path), args}, t) =
         pathCoercion env pos Up (path, Vector1.toVector args) t

      | coercion env pos (t, App {callee = SVar (Path path), args}) =
         pathCoercion env pos Down (path, Vector1.toVector args) t

      | coercion env pos (App {callee, args}, App {callee = callee', args = args'}) =
         Vector1.foldl (fn ((arg, arg'), calleeCoercion) =>
                            CompCo (calleeCoercion, coercion env pos (arg, arg')))
                       (coercion env pos (callee, callee'))
                       (Vector1.zip (args, args')) (* FIXME: Arity errors *)

      | coercion env pos (CallTFn (name, args), CallTFn (name', args')) =
         (* FIXME: Arity errors: *)
         CallTFnCo (name, Vector.zipWith (coercion env pos) (args, args'))

      | coercion env pos (l as UseT {var, kind}, r as UseT {var = var', kind = kind'}) =
         (* TODO: Go back to using `OVar` => this becomes `raise Fail "unreachable" *)
         if not (var = var')
         then raise TypeError (NonUnifiable (pos, l, r, NONE))
         else if not (idInScope env var)
              then raise TypeError (OutsideScope (pos, Name.fromString ("g__" ^ Id.toString var)))
              else if not (kind = kind')
                   then raise TypeError (InequalKinds (pos, kind, kind'))
                   else Refl l

      | coercion env pos (SVar (OVar ov), SVar (OVar ov')) = raise Fail "unimplemented"

      | coercion env pos (SVar (UVar uv), r as SVar (UVar uv')) =
         (case (Uv.get uv, Uv.get uv')
          of (Right l, Right r) => coercion env pos (l, r)
           | (Left uv, Right t) | (Right t, Left uv) =>
              solution env pos (uv , t)
           | (Left uv, Left uv') =>
              let val kind = Uv.kind uv
                  val kind' = Uv.kind uv'
              in if not (kind = kind')
                 then raise TypeError (InequalKinds (pos, kind, kind'))
                 else ()
               ; uvMerge env (uv, uv')
               ; Refl r
              end)

      | coercion env pos ((SVar (UVar uv), t) | (t, SVar (UVar uv))) =
         (case Uv.get uv
          of Right t' => coercion env pos (t, t')
           | Left uv => solution env pos (uv, t))

      | coercion env pos (SVar (Path path), SVar (Path path')) =
         pathsCoercion env pos ((path, #[]), (path', #[]))

      | coercion env pos (SVar (Path path), t) = pathCoercion env pos Up (path, #[]) t

      | coercion env pos (t, SVar (Path path)) = pathCoercion env pos Down (path, #[]) t

      | coercion env pos (l as Prim p, r as Prim p') =
         if p = p'
         then Refl r
         else raise TypeError (NonUnifiable (pos, l, r, NONE))

      | coercion env pos (l, r) = raise TypeError (NonUnifiable (pos, l, r, NONE))

    and solution env pos (uv, t) =
        ( if occurs env uv t
          then raise TypeError (Occurs (pos, SVar (UVar uv), t))
          else ()
        ; checkMonotypeKind env pos (Uv.kind uv) t
        ; uvSet env (uv, t)
        ; Refl t )

    and pathsCoercion env pos ((path, args), (path', args')) =
        case (pathGet env path, pathGet env path')
        of (Right (impl, coDef), Right (impl', coDef')) =>
            raise Fail "unimplemented"
         | (Right _, Left face') =>
            pathCoercion env pos Up (path, args) (applyType face' args')
         | (Left face, Right _) =>
            pathCoercion env pos Down (path', args') (applyType face args)
         | (Left face, Left face') =>
            let val face = applyType face args
                val face' = applyType face' args'
            in coercion env pos (face, face')
            end

    and pathCoercion env pos direction (path, args) t =
        case pathGet env path
        of Right (impl, coDef) =>
            let val face = applyType (Path.face path) args
                val revealCo = instantiateCoercion (UseCo coDef) args
            in  case direction
                of Up => Trans (revealCo, coercion env pos (SVar (UVar impl), t))
                 | Down => Trans (coercion env pos (SVar (UVar impl), t), Symm revealCo)
            end
            
         | Left face =>
            let val face = applyType face args
            in  case direction
                of Up => coercion env pos (face, t)
                 | Down => coercion env pos (t, face)
            end

(* # Subtyping *)

    (* Check that `typ` <: `superTyp` and return the coercer if any. *)
    and subType env pos (typs as (sub, super)) =
        coercer env pos typs
        handle TypeError cause =>
                ( Env.error env (NonSubType (pos, sub, super, SOME cause))
                ; SOME (fn expr =>
                            let val pos = FTerm.exprPos expr
                                val def = { pos, id = DefId.fresh (), var = Name.fresh ()
                                          , typ = super }
                            in FTerm.Let ( FTerm.exprPos expr
                                         , valOf (Vector1.fromVector #[FTerm.Val (pos, def, expr)])
                                         , FTerm.Use (pos, def) )
                            end) )

    and coercer env pos (sub as Exists existential, super) =
         raise Fail "unimplemented"

      | coercer env pos (sub, super as Exists existential) =
         raise Fail "unimplemented"

      | coercer env pos (sub, super as ForAll universal) =
         skolemize env universal (fn (env, params, body) =>
             Option.map (fn coerce => fn expr => FTerm.TFn (pos, params, coerce expr))
                        (coercer env pos (sub, body))
         )

      | coercer env pos (sub as ForAll universal, super) =
         instantiate env universal (fn (env, args, body) =>
             Option.map (fn coerce => fn expr =>
                             coerce (FTerm.TApp (pos, body, {callee = expr, args})))
                        (coercer env pos (body, super))
         )

      | coercer env pos (sub, Arrow (Implicit, {domain, codomain})) =
         let val def = {pos, id = DefId.fresh (), var = Name.fresh (), typ = domain}
             val coerceCodomain = coercer env pos (sub, codomain)
         in SOME (fn expr => FTerm.Fn (pos, def, Implicit, applyCoercion coerceCodomain expr))
         end

      | coercer env pos (Arrow (Implicit, {domain, codomain}), super) =
         (* FIXME: coercer from `codomain` <: `super` *)
         (case domain
          of FType.Type domain =>
              let val arg = FTerm.Type (pos, domain)
              in SOME (fn expr => FTerm.App (pos, codomain, {callee = expr, arg}))
              end
           | _ => raise Fail "implicit parameter not of type `type`")

      | coercer env pos ( Arrow (Explicit eff, domains as {domain, codomain})
                        , Arrow (Explicit eff', domains' as {domain = domain', codomain = codomain'}) ) =
         let do subEffect pos (eff, eff')
             val coerceDomain = coercer env pos (domain', domain)
             val coerceCodomain = coercer env pos (codomain, codomain')
         in if isSome coerceDomain orelse isSome coerceCodomain
            then SOME (fnCoercion coerceDomain coerceCodomain
                                  ((eff, domains), (eff', domains')))
            else NONE
         end

      | coercer env pos (sub as Record row, super as Record row') =
         let val tmpDef = {pos, id = DefId.fresh (), var = Name.fresh (), typ = sub}
             val tmpUse = FTerm.Use (pos, tmpDef)

             val rec recCoercer =
                 fn (row, row' as RowExt {base = base', field = (label, fieldt')}, tail) =>
                     let val {base, fieldt} = reorderRow pos label row
                         val row = RowExt {base, field = (label, fieldt')}
                         val t = Record row
                         val {base = tail, ...} = reorderRow pos label tail
                     in  case coercer env pos (fieldt, fieldt')
                         of SOME coerceField =>
                             let val fieldExpr = coerceField (FTerm.Field (pos, fieldt, tmpUse, label))
                                 val nextCoerce = recCoercer (row, base', tail)
                             in  SOME (fn expr =>
                                           let val expr =
                                                   FTerm.Where (pos, t, { base = expr
                                                                        , field = (label, fieldExpr) })
                                           in applyCoercion nextCoerce expr
                                           end)
                             end
                          | NONE => recCoercer (row, base', tail)
                     end
                  | (_, row', tail) => (* FIXME: What about WildRow?!: *)
                     ( coercion env pos (tail, row')
                     ; NONE )
         in  case recCoercer (row, row', row)
             of SOME coerce =>
                 SOME (fn expr =>
                           FTerm.Let ( pos
                                     , valOf (Vector1.fromVector #[FTerm.Val (pos, tmpDef, expr)])
                                     , coerce tmpUse ))
              | NONE => NONE
         end

      | coercer env pos (sub as RowExt _, super as RowExt {base = base', field = (label, fieldt')}) =
         let val {base, fieldt} = reorderRow pos label sub
             (* No values of row type exist => coercer unnecessary: *)
             do ignore (coercer env pos (fieldt, fieldt'))
             do ignore (coercer env pos (base, base'))
         in NONE
         end

      | coercer env pos (EmptyRow, EmptyRow) = NONE

      | coercer env pos (Type sub, Type super) =
         ( coercer env pos (sub, super)
         ; coercer env pos (super, sub)
         ; SOME (fn _ => FTerm.Type (pos, super)) )

      | coercer env pos ( App {callee = SVar (Path path), args}
                        , App {callee = SVar (Path path'), args = args'} ) =
         pathsCoercer env pos ((path, Vector1.toVector args), (path', Vector1.toVector args'))

      | coercer env pos (App {callee = SVar (Path path), args}, super) =
         pathCoercer env pos Up (path, Vector1.toVector args) super

      | coercer env pos (sub, App {callee = SVar (Path path), args}) =
         pathCoercer env pos Down (path, Vector1.toVector args) sub

      | coercer env pos (App {callee, args}, App {callee = callee', args = args'}) =
         ( ignore (coercer env pos (callee, callee'))
         ; Vector1.app (ignore o coercer env pos)
                       (Vector1.zip (args, args'))
         ; NONE )

      | coercer env pos (sub as CallTFn (callee, args), super as CallTFn (callee', args')) =
         if callee = callee'
         then ( Vector.app (ignore o coercion env pos) (Vector.zip (args, args'))
              ; Vector.app (ignore o coercion env pos) (Vector.zip (args', args))
              ; NONE ) (* Since both callee and args have to unify, coercer is always no-op. *)
         else raise TypeError (NonSubType (pos, sub, super, NONE))

      | coercer env pos (sub as UseT {var, ...}, super as UseT {var = var', ...}) =
         (* TODO: Go back to using `OVar` => this becomes `raise Fail "unreachable" *)
         if var = var'
         then if idInScope env var
              then NONE
              else raise TypeError (OutsideScope ( pos
                                                 , Name.fromString ("g__" ^ Id.toString var) ))
         else raise TypeError (NonSubType (pos, sub, super, NONE))

      | coercer env pos (SVar (OVar ov), SVar (OVar ov')) =
         raise Fail "unimplemented"

      | coercer env pos (SVar (UVar uv), SVar (UVar uv')) =
         (case (Uv.get uv, Uv.get uv')
          of (Right t, Right t') => coercer env pos (t, t')
           | (Left uv, Right t) => assign env pos (Up, uv, t)
           | (Right t, Left uv) => assign env pos (Down, uv, t)
           | (Left uv, Left uv') =>
              let val kind = Uv.kind uv
                  val kind' = Uv.kind uv'
              in if not (kind = kind')
                 then raise TypeError (InequalKinds (pos, kind, kind'))
                 else ()
               ; uvMerge env (uv, uv')
               ; NONE
              end)

      | coercer env pos (SVar (UVar uv), super) =
         (case Uv.get uv
          of Left uv => assign env pos (Up, uv, super)
           | Right sub => coercer env pos (sub, super))

      | coercer env pos (sub, SVar (UVar uv)) =
         (case Uv.get uv
          of Left uv => assign env pos (Down, uv, sub)
           | Right super => coercer env pos (sub, super))

      | coercer env pos (SVar (Path path), SVar (Path path')) =
         pathsCoercer env pos ((path, #[]), (path', #[]))

      | coercer env pos (SVar (Path path), super) =
         pathCoercer env pos Up (path, #[]) super

      | coercer env pos (sub, SVar (Path path)) =
         pathCoercer env pos Down (path, #[]) sub

      | coercer env pos (sub as Prim p, super as Prim p') =
         if p = p'
         then NONE
         else raise TypeError (NonSubType (pos, sub, super, NONE))

      | coercer env pos (sub, super) = raise TypeError (NonSubType (pos, sub, super, NONE))

    and subEffect pos effs =
        case effs
        of (Pure, Pure) => ()
         | (Pure, Impure) => ()
         | (Impure, Pure) => raise Fail "Impure is not a subtype of Pure"
         | (Impure, Impure) => ()

    and pathsCoercer env pos ((path, args), (path', args')) =
        case (pathGet env path, pathGet env path')
        of (Right (impl, coDef), Right (impl', coDef')) =>
            raise Fail "unimplemented"
         | (Right _, Left face') =>
            pathCoercer env pos Up (path, args) (applyType face' args')
         | (Left face, Right _) =>
            pathCoercer env pos Down (path', args') (applyType face args)
         | (Left face, Left face') =>
            let val face = applyType face args
                val face' = applyType face' args'
            in coercer env pos (face, face')
            end

    and pathCoercer env pos direction (path, args) t =
        case pathGet env path
        of Right (impl, coDef) =>
            let val face = applyType (Path.face path) args
                val revealCo = instantiateCoercion (UseCo coDef) args
            in  case direction
                of Up =>
                    let fun reveal expr = Cast (exprPos expr, SVar (UVar impl), expr, revealCo)
                    in  case coercer env pos (SVar (UVar impl), t)
                        of SOME fromImpl => SOME (fromImpl o reveal)
                         | NONE => SOME reveal
                    end
                 | Down =>
                    let fun hide expr = Cast (exprPos expr, face, expr, Symm revealCo)
                    in  case coercer env pos (t, SVar (UVar impl))
                        of SOME toImpl => SOME (hide o toImpl)
                         | NONE => SOME hide
                    end
            end

         | Left face =>
            let val face = applyType face args
            in  case direction
                of Up => coercer env pos (face, t)
                 | Down => coercer env pos (t, face)
            end

(* ## Unification Variable Sub/Super-solution *)

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
    and assign (env: Env.t) pos (y: direction, uv: concr TypeVars.uv, t: concr): coercer =
        if Concr.occurs (Env.hasScope env) uv t
        then raise TypeError (Occurs (pos, SVar (UVar uv), t))
        else doAssign env pos y (uv, t)

    and doAssign (env: Env.t) pos (y: direction) (uv, t: concr): coercer =
        case t
        of ForAll args => doAssignUniversal env pos y uv args
         | Arrow (Explicit eff, domains) => doAssignArrow env y uv pos eff domains
         | RowExt _ | EmptyRow | Record _ | CallTFn _ | Prim _ | Type _ => (uvSet env (uv, t); NONE)
         | UseT {var, ...} => 
            ( uvSet env (uv, t)
            ; if idInScope env var
              then NONE
              else raise TypeError (OutsideScope (pos, Name.fromString ("g__" ^ Id.toString var))) )
         | SVar (OVar ov) =>
            ( uvSet env (uv, t)
            ; if Env.hasScope env (TypeVars.Ov.scope ov)
              then NONE
              else raise TypeError (OutsideScope (pos, TypeVars.Ov.name ov)) )
         | SVar (UVar uv') =>
            ( case Uv.get uv'
              of Left _ => uvSet env (uv, t)
               | Right t => uvSet env (uv, t)
            ; NONE )
         | SVar (Path _) => (uvSet env (uv, t); NONE)

    and doAssignUniversal env pos (y: direction) uv (universal as (_, _)) =
        case y
        of Up =>
            skolemize env universal (fn (env, params, body) =>
                Option.map (fn coerce => fn expr => FTerm.TFn (pos, params, coerce expr))
                           (doAssign env pos y (uv, body))
            )
         | Down =>
            instantiate env universal (fn (env, args, body) =>
                Option.map (fn coerce => fn callee => coerce (FTerm.TApp (pos, body, {callee, args})))
                           (doAssign env pos y (uv, body))
            )

    and doAssignArrow (env: Env.t) (y: direction) uv pos eff (arrow as {domain, codomain}) =
        let val domainUv = TypeVars.Uv.freshSibling uv
            val codomainUv = TypeVars.Uv.freshSibling uv
            val arrow' = { domain = SVar (UVar domainUv)
                         , codomain = SVar (UVar codomainUv)}
            val t' = Arrow (Explicit eff, arrow')
            do ignore (uvSet env (uv, t'))
            val coerceDomain = assign env pos (flip y, domainUv, domain) (* contravariance *)
            val coerceCodomain = assign env pos (y, codomainUv, codomain)
        in if isSome coerceDomain orelse isSome coerceCodomain
           then let val arrows = case y
                                 of Up => ((eff, arrow'), (eff, arrow))
                                  | Down => ((eff, arrow), (eff, arrow'))
                in SOME (fnCoercion coerceDomain coerceCodomain arrows)
                end
           else NONE
        end
end

