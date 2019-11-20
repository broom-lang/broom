structure TypecheckingOps :> sig (* HACK: Dependency chains, grrr... *)
    type env = (FlexFAst.Type.concr, FlexFAst.Term.expr, TypeError.t) TypecheckingEnv.t

    val rowWhere : (env -> Pos.span -> FlexFAst.Type.concr * FlexFAst.Type.concr -> unit)
        -> env -> Pos.span -> (FlexFAst.Type.concr * (Name.t * FlexFAst.Type.concr))
        -> FlexFAst.Type.concr
    val checkMonotypeKind : env -> Pos.span -> FlexFAst.Type.kind -> FlexFAst.Type.concr -> unit
end = struct
    datatype typ = datatype FType.concr
    structure FType = FlexFAst.Type
    structure FTerm = FlexFAst.Term
    datatype sv = datatype FType.sv
    structure Env = TypecheckingEnv
    type env = (FlexFAst.Type.concr, FlexFAst.Term.expr, TypeError.t) TypecheckingEnv.t
    structure Uv = TypeVars.Uv
    structure Path = TypeVars.Path
    open TypeError
    val op|> = Fn.|>

    fun rowWhere subType env pos (row, field' as (label', fieldt')) =
        case row
        of RowExt {base, field = field as (label, fieldt)} =>
            if label = label'
            then let do subType env pos (fieldt', fieldt)
                 in RowExt {base, field = (label, fieldt')}
                 end
            else RowExt {base = rowWhere subType env pos (row, field'), field}

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

