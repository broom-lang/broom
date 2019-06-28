structure Subtyping :> sig
    type coercion = (FlexFAst.Term.expr -> FlexFAst.Term.expr) option
   
    val applyCoercion: coercion -> FlexFAst.Type.sv FAst.Term.expr -> FlexFAst.Type.sv FAst.Term.expr
    val subType: TypecheckingEnv.t -> Pos.t -> FlexFAst.Type.concr * FlexFAst.Type.concr -> coercion
end = struct
    datatype predicativity = datatype TypeVars.predicativity
    structure FType = FAst.Type
    datatype abs = datatype FType.abs
    val concr = FType.Abs.concr
    structure FTerm = FAst.Term
    structure Env = TypecheckingEnv
    open TypeError

    fun idInScope env id = isSome (Env.findType env id)

    fun uvSet env =
        TypeVars.Uv.set FlexFAst.Type.Concr.tryToUv Env.Scope.Id.compare (Env.hasScope env)

    fun pathSet env =
        TypeVars.Path.set (Name.fromString o FlexFAst.Type.Concr.toString) (* HACK *)
                          (Env.hasScope env)

    type coercion = (FlexFAst.Term.expr -> FlexFAst.Term.expr) option
    type field_coercion = Name.t * (FlexFAst.Type.sv FTerm.expr -> FlexFAst.Type.sv FTerm.expr)

    fun applyCoercion (coerce: coercion) expr =
        case coerce
        of SOME f => f expr
         | NONE => expr

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
    fun assign (env: Env.t) (y, uv: (Env.Scope.Id.t, FlexFAst.Type.concr) TypeVars.uv, t: FlexFAst.Type.concr): unit =
        if FlexFAst.Type.Concr.occurs uv t
        then raise TypeError (Occurs (FType.SVar (FType.Concr.pos t, FlexFAst.Type.UVar uv), concr t))
        else doAssign env y (uv, t)

    and doAssign (env: Env.t) y (uv, t: FlexFAst.Type.concr) =
        case t
        of FType.Arrow (pos, domains) => doAssignArrow env y uv pos domains
         | FType.RowExt _ => uvSet env (uv, t) (* FIXME: row kind check, t smallness check *)
         | FType.EmptyRow _ => uvSet env (uv, t) (* FIXME: Check that uv is of row kind. *)
         | FType.Prim _ => uvSet env (uv, t)
         | FType.UseT (_, {var, ...}) => 
            if idInScope env var
            then uvSet env (uv, t)
            else raise Fail ("Opaque type out of scope: g__" ^ Id.toString var)
         | FType.SVar (_, FlexFAst.Type.UVar uv') =>
            (case TypeVars.Uv.get uv'
             of Either.Left uv' => uvSet env (uv, t)
              | Either.Right t => uvSet env (uv, t))

    and doAssignArrow (env: Env.t) y uv pos {domain, codomain} =
        let val domainUv = Env.freshUv env Predicative
            val codomainUv = Env.freshUv env Predicative
            val t' = FType.Arrow (pos, { domain = FType.SVar (pos, FlexFAst.Type.UVar domainUv)
                                       , codomain = FType.SVar (pos, FlexFAst.Type.UVar codomainUv)})
        in uvSet env (uv, t')
         ; assign env (flipY y, domainUv, domain) (* contravariance *)
         ; assign env (y, codomainUv, codomain)
        end

    (* Check that `typ` <: `superTyp` and return the coercion if any. *)
    fun subType (env: Env.t) currPos (typ: FlexFAst.Type.concr, superTyp: FlexFAst.Type.concr): coercion =
        case (typ, superTyp)
        of (_, FType.ForAll (_, params, body)) =>
            let val params' = Vector.map (fn {kind, ...} => {var = Id.fresh (), kind}) params
                val env =
                    Vector.foldl (fn (def, env) =>
                                      Env.pushScope env (Env.Scope.ForAllScope (Env.Scope.Id.fresh (), def)))
                                 env params'
                val mapping =
                    Vector.foldl (fn (({var, ...}, def'), mapping) =>
                                      Id.SortedMap.insert (mapping, var, FType.UseT (currPos, def')))
                                 Id.SortedMap.empty
                                 (Vector.zip (params, params'))
                val body = FlexFAst.Type.Concr.substitute mapping body
            in Option.map (fn coerce => fn expr => FTerm.TFn (currPos, params', coerce expr))
                          (subType env currPos (typ, body))
            end
         | (FType.ForAll (_, params, body), _) =>
           let val env = Env.pushScope env (Env.Scope.Marker (Env.Scope.Id.fresh ()))
               val args = Vector.map (fn _ => FType.SVar (currPos, FlexFAst.Type.UVar (Env.freshUv env Predicative)))
                                     params
               val mapping =
                   Vector.foldl (fn (({var, ...}, arg), mapping) => Id.SortedMap.insert (mapping, var, arg))
                                Id.SortedMap.empty
                                (Vector.zip (params, args))
               val body = FlexFAst.Type.Concr.substitute mapping body
           in Option.map (fn coerce => fn expr => coerce (FTerm.TApp (currPos, body, {callee = expr, args})))
                         (subType env currPos (body, superTyp))
           end
         | (FType.Arrow (_, arr), FType.Arrow (_, arr')) => subArrows env currPos (arr, arr')
         | (FType.Record (_, row), FType.Record (_, row')) => 
            (case subRows env currPos (row, row')
             of [] => NONE)
         | (FType.RowExt _, FType.RowExt _) =>
           ( subRows env currPos (typ, superTyp)
           ; NONE ) (* No values of row type exist => coercion unnecessary *)
         | (FType.EmptyRow _, FType.EmptyRow _) => NONE
         | (FType.Prim (_, pl), FType.Prim (_, pr)) =>
            if pl = pr
            then NONE
            else raise Fail "<:"
         | (FType.Type (pos, FType.Exists (_, #[], t)), FType.Type (_, sup as FType.Exists (_, #[], t'))) =>
            (* TODO: Actual existentials (with params). *)
            (* TODO: Replace <: + :> with plain unification: *)
            ( subType env currPos (t, t')
            ; subType env currPos (t', t)
            ; SOME (fn _ => FTerm.Type (pos, sup)))
         | (FType.UseT (_, {var, ...}), FType.UseT (_, {var = var', ...})) =>
            if var = var'
            then if idInScope env var
                 then NONE
                 else raise Fail ("Opaque type out of scope: " ^ FlexFAst.Type.Concr.toString superTyp)
            else raise TypeError (NonSubType (currPos, concr typ, concr superTyp))
         | (FType.SVar (_, FlexFAst.Type.UVar uv), FType.SVar (_, FlexFAst.Type.UVar uv')) =>
            (case (TypeVars.Uv.get uv, TypeVars.Uv.get uv')
             of (Either.Left uv, Either.Left _) =>
                 (uvSet env (uv, superTyp); NONE) (* Call `uvSet` directly to skip occurs check. *)
              | (Either.Left uv, Either.Right t) => (assign env (Sub, uv, t); NONE)
              | (Either.Right t, Either.Left uv) => (assign env (Super, uv, t); NONE)
              | (Either.Right t, Either.Right t') => subType env currPos (t, t'))
         | (FType.SVar (_, FlexFAst.Type.UVar uv), _) => subUv env currPos uv superTyp
         | (_, FType.SVar (_, FlexFAst.Type.UVar uv)) => superUv env currPos uv typ
         | (_, FType.SVar (_, FlexFAst.Type.Path path)) => suberPath env currPos Super path typ
         | (FType.SVar (_, FlexFAst.Type.Path path), _) => suberPath env currPos Sub path superTyp
         | _ => raise Fail ("unimplemented: " ^ FlexFAst.Type.Concr.toString typ ^ " <: "
                            ^ FlexFAst.Type.Concr.toString superTyp)

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

    and subRows env currPos (rows: FlexFAst.Type.concr * FlexFAst.Type.concr): field_coercion list =
        let val rec subExts =
                fn (row, FType.RowExt (_, {field = (label, fieldt'), ext = ext'})) =>
                    let val (fieldt, ext) = reorderRow currPos label (FType.rowExtTail ext') row
                        val coerceField = subType env currPos (fieldt, fieldt')
                        val coerceExt = subExts (ext, ext')
                    in case coerceField
                       of SOME coerceField => (label, coerceField) :: coerceExt
                        | NONE => coerceExt
                    end
                 | rows => (subType env currPos rows; [])
        in subExts rows
        end

    and reorderRow currPos label (tail: FlexFAst.Type.concr): FlexFAst.Type.concr -> FlexFAst.Type.concr * FlexFAst.Type.concr =
        fn FType.RowExt (pos, {field = (label', fieldt'), ext = ext}) =>
            if label = label'
            then (fieldt', ext)
            else let val (fieldt, ext) = reorderRow currPos label tail ext
                 in (fieldt, FType.RowExt (pos, {field = (label', fieldt'), ext = ext}))
                 end
         (* FIXME: `t` is actually row tail, not the type of `expr`. *)
         | t => raise TypeError (MissingField (currPos, t, label))

    and subUv env currPos uv superTyp = case TypeVars.Uv.get uv
                                        of Either.Left uv => (assign env (Sub, uv, superTyp); NONE)
                                         | Either.Right t => subType env currPos (t, superTyp)

    and superUv env currPos uv subTyp = case TypeVars.Uv.get uv
                                        of Either.Left uv => (assign env (Super, uv, subTyp); NONE)
                                         | Either.Right t => subType env currPos (subTyp, t)

    and suberPath env currPos y path t =
        case TypeVars.Path.get (Env.hasScope env) path
        of Either.Left (face, NONE) => subType env currPos (case y
                                                            of Sub => (face, t)
                                                             | Super => (t, face))
         | Either.Left (face, SOME coercionDef) => (* FIXME: enforce predicativity: *)
            if FlexFAst.Type.Concr.pathOccurs path t
            then raise TypeError (Occurs (face, concr t))
            else ( pathSet env (path, t)
                 ; SOME (pathCoercion y coercionDef) )
         | Either.Right (typ, coercionDef) => SOME (pathCoercion y coercionDef)

    and pathCoercion y coercionDef =
        case y
        of Sub => (fn expr => FTerm.Cast (FTerm.exprPos expr, expr, FType.UseCo coercionDef))
         | Super => (fn expr => FTerm.Cast (FTerm.exprPos expr, expr, FType.Symm (FType.UseCo coercionDef)))
end

