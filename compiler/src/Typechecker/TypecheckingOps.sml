structure TypecheckingOps :> sig (* HACK: Dependency chains, grrr... *)
    structure FType : CLOSED_FAST_TYPE
        where type sv = FlexFAst.Type.sv
    type env = (FlexFAst.Type.concr, FlexFAst.Term.expr, TypeError.t) TypecheckingEnv.t

    val rowWhere : (env -> Pos.span -> FType.concr -> Name.t -> FType.concr * FType.concr -> FType.concr)
        -> env -> Pos.span -> (FType.concr * (Name.t * FType.concr)) -> FType.concr
    val rowWithout : env -> Pos.span -> (FType.concr * Name.t) -> FType.concr
    val instantiate : env -> FType.def vector * FType.concr
        -> (env * FType.concr vector * FType.concr -> 'a) -> 'a
    val checkMonotypeKind : env -> Pos.span -> FlexFAst.Type.kind -> FlexFAst.Type.concr -> unit
end = struct
    datatype typ = datatype FType.concr
    structure FType = FlexFAst.Type
    structure Concr = FType.Concr
    structure FTerm = FlexFAst.Term
    datatype sv = datatype FType.sv
    structure Env = TypecheckingEnv
    structure Scope = Env.Scope
    type env = (FlexFAst.Type.concr, FlexFAst.Term.expr, TypeError.t) TypecheckingEnv.t
    structure Uv = TypeVars.Uv
    structure Path = TypeVars.Path
    open TypeError
    val op|> = Fn.|>

    fun rowWhere override env pos (row, field' as (label', fieldt')) =
        case row
        of RowExt {base, field = field as (label, fieldt)} =>
            if label = label'
            then override env pos base label (fieldt', fieldt)
            else RowExt {base = rowWhere override env pos (base, field'), field}

    fun rowWithout env pos (row, label') =
        case row
        of RowExt {base, field = field as (label, _)} =>
            if label = label'
            then base
            else RowExt {base = rowWithout env pos (base, label'), field}

    (* \forall|\exists a... . T --> [(\hat{a}/a)...]T and push \hat{a}... to env *)
    fun instantiate env (params: FType.def vector, body) f =
        let val env = Env.pushScope env (Scope.Marker (Scope.Id.fresh ()))
            val args = Vector.map (fn {kind, ...} => SVar (UVar (Uv.fresh env kind)))
                                  params
            val mapping = (params, args)
                        |> Vector.zipWith (fn ({var, kind = _}, arg) => (var, arg))
                        |> FType.Id.SortedMap.fromVector
            val body = Concr.substitute env mapping body
        in f (env, args, body)
        end

    fun monotypeKind env pos =
        fn t as Exists _ | t as ForAll _ => raise TypeError (NonMonotype (pos, t))
         | Arrow (_, {domain, codomain}) =>
            ( checkMonotypeKind env pos FType.TypeK domain
            ; checkMonotypeKind env pos FType.TypeK codomain
            ; FType.TypeK )
         | Record row =>
            ( checkMonotypeKind env pos FType.RowK row
            ; FType.TypeK )
         | RowExt {base, field = (_, fieldt)} =>
            ( checkMonotypeKind env pos FType.RowK base
            ; checkMonotypeKind env pos FType.TypeK fieldt
            ; FType.TypeK )
         | EmptyRow => FType.RowK
         | Type t =>
            ( checkMonotypeKind env pos FType.TypeK t
            ; FType.TypeK )
         | App {callee, args} =>
            let fun checkArgKind i calleeKind =
                    if i < Vector1.length args
                    then case calleeKind
                         of FType.ArrowK {domain, codomain} =>
                             ( checkMonotypeKind env pos domain (Vector1.sub (args, i))
                             ; checkArgKind (i + 1) codomain )
                          | _ => raise TypeError (TypeCtorArity (pos, callee, calleeKind, Vector1.length args))
                    else calleeKind
            in checkArgKind 0 (monotypeKind env pos callee)
            end
         | CallTFn {kind, ...} => kind
         | SVar (UVar uv) => Uv.kind env uv
         | SVar (Path path) => Path.kind path
         | UseT {var, kind} => (* TODO: Should be unreachable on return of Ov: *)
            if isSome (Env.findType env var)
            then kind
            else raise TypeError (OutsideScope (pos, var |> FType.Id.toString |> Name.fromString))
         | Prim _ => FType.TypeK

    and checkMonotypeKind env pos kind t =
        let val kind' = monotypeKind env pos t
        in  if kind' = kind
            then ()
            else raise TypeError (InequalKinds (pos, kind', kind))
        end
end

