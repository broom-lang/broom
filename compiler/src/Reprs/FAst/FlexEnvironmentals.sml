structure FlexEnvironmentals :> sig
    structure Type : CLOSED_FAST_TYPE where type sv = FlexFAst.Type.sv
    structure Id : ID
        where type t = FType.Id.t
        where type 'v SortedMap.map = 'v FType.Id.SortedMap.map

    structure Concr : sig
        val substitutePath : (TypecheckingEnv.Scope.Id.t -> bool)
                             -> (Type.concr * Type.concr -> unit)
                             -> Type.concr Id.SortedMap.map -> Type.concr -> Type.concr
    end
end = struct
    structure Type = FlexFAst.Type
    structure Id = FType.Id
    datatype concr = datatype FType.concr

    fun concrSubstitutePath hasScope unifyArg mapping =
        let fun subst mapping =
                fn t as ForAll (_, params, _) =>
                    let val mapping = Vector.foldl (fn ({var, ...}, mapping) =>
                                                        (#1 (Id.SortedMap.remove (mapping, var)))
                                                        handle _ => mapping)
                                                   mapping params
                    in FType.Concr.mapChildren (subst mapping) t
                    end
                 | t as App (pos, {callee = UseT (_, {var, ...}), args}) =>
                    (case Id.SortedMap.find (mapping, var)
                     of SOME t' =>
                         (case t'
                          of SVar (_, Type.Path path) =>
                              (case TypeVars.Path.face path
                               of App (_, {callee = _, args = faceArgs}) =>
                                   ( Vector.zipWith unifyArg (args, faceArgs)
                                   ; t' )
                                | _ => raise Fail "unreachable")
                           | _ => raise Fail "unreachable")
                      | NONE => FType.Concr.mapChildren (subst mapping) t)
                 | t as (Arrow _ | Record _ | RowExt _ | EmptyRow _ | CallTFn _ | App _ | Prim _) =>
                    FType.Concr.mapChildren (subst mapping) t
                 | Type (pos, t) => Type (pos, FType.Abs.substitute (Type.Concr.svarSubstitute hasScope) mapping t)
                 | t as UseT (_, {var, ...}) => getOpt (Id.SortedMap.find (mapping, var), t)
                 | t as SVar (_, sv) => getOpt (Type.Concr.svarSubstitute hasScope mapping sv, t)
        in subst mapping
        end

    structure Concr = struct
        val substitutePath = concrSubstitutePath
    end
end

