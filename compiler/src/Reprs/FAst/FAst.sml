structure FlexFAst = struct
    structure ScopeId = ScopeId

    val text = PPrint.text
    val op<> = PPrint.<>

    structure Type = struct
        open FType
        structure ScopeId = ScopeId

        datatype concr' = datatype FType.concr
        datatype co' = datatype FType.co

        datatype sv = OVar of ov | UVar of uv | Path of path
        withtype concr = sv FType.concr
        and co = sv FType.co
        and ov = TypeVars.ov
        and uv = sv FType.concr TypeVars.uv
        and path = sv FType.concr TypeVars.path

        val rec concrToDoc = fn t => FType.Concr.toDoc svarToDoc t
        and svarToDoc =
            fn Path path =>
                (case TypeVars.Path.get (Fn.constantly false) path
                 of Either.Right (uv, _) => uvToDoc uv
                  | Either.Left t => text "^^" <> PPrint.parens (concrToDoc t))
             | OVar ov => Name.toDoc (TypeVars.Ov.name ov)
             | UVar uv => uvToDoc uv
        and uvToDoc = fn uv =>
            case TypeVars.Uv.get uv
            of Either.Right t => concrToDoc t
             | Either.Left uv => text "^" <> Name.toDoc (TypeVars.Uv.name uv)

        structure Concr = struct
            open Concr

            datatype t = datatype concr

            val toDoc = concrToDoc
            val toString = toString svarToDoc

            fun occurs hasScope uv = FType.Concr.occurs (svarOccurs hasScope) uv
            and svarOccurs hasScope uv =
                fn Path path =>
                    (case TypeVars.Path.get hasScope path
                     of Either.Left t => occurs hasScope uv t
                      | Either.Right (uv', _) => uvOccurs hasScope uv uv')
                 | OVar _ => false
                 | UVar uv' => uvOccurs hasScope uv uv'
            and uvOccurs hasScope uv uv' =
                case TypeVars.Uv.get uv'
                of Either.Left uv' => TypeVars.Uv.eq (uv, uv')
                 | Either.Right t => occurs hasScope uv t

            fun pathOccurs path = FType.Concr.occurs pathSvarOccurs path
            and pathSvarOccurs path =
                fn Path path' => TypeVars.Path.eq (path', path)
                 | OVar _ => false
                 | UVar uv => (case TypeVars.Uv.get uv
                               of Either.Left uv => false
                                | Either.Right t => pathOccurs path t)

            fun substitute hasScope kv = FType.Concr.substitute (svarSubstitute hasScope) kv
            and svarSubstitute hasScope kv =
                fn Path path =>
                    (case TypeVars.Path.get hasScope path
                     of Either.Left _ => NONE (* path faces are always CallTFn:s with OVar args *)
                      | Either.Right (uv, _) => uvSubstitute hasScope kv uv)
                 | OVar _ => NONE
                 | UVar uv => uvSubstitute hasScope kv uv
            and uvSubstitute hasScope kv uv =
                case TypeVars.Uv.get uv
                of Either.Left _ => NONE
                 | Either.Right t => SOME (substitute hasScope kv t)

            val tryToUv =
                fn SVar (UVar uv) => SOME uv
                 | _ => NONE
        end

        structure Co = struct
            open Co

            val toDoc = toDoc svarToDoc
        end
    end

    structure Term = FTerm(Type)
end

structure FixedFAst = struct
    structure ScopeId = FlexFAst.ScopeId

    structure Type = struct
        open FType
        structure ScopeId = ScopeId

        datatype concr' = datatype FType.concr
        datatype co' = datatype FType.co

        type sv = Nothing.t
        type concr = sv concr
        type co = sv co'

        val svarToDoc = PPrint.text o Nothing.toString

        val concrToString: concr -> string = FType.Concr.toString svarToDoc

        structure Concr = struct
            open Concr

            datatype t = datatype concr

            val toDoc = toDoc svarToDoc
            val substitute = fn hasScope => substitute (fn _ => fn _ => NONE)
            val kindOf: concr -> kind = kindOf (fn _ => raise Fail "unreachable")
            val toString = concrToString
        end

        structure Co = struct
            open Co
            
            val toDoc = toDoc svarToDoc
        end
    end

    structure Term = FTerm(Type)
end

