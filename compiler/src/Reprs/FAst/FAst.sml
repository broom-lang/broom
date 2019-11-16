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

        fun concrToDoc env = fn t => FType.Concr.toDoc (svarToDoc env) t
        and svarToDoc env =
            fn Path path =>
                (case TypeVars.Path.get env path
                 of Either.Right (uv, _) => uvToDoc env uv
                  | Either.Left t => text "^^" <> PPrint.parens (concrToDoc env t))
             | OVar ov => Name.toDoc (TypeVars.Ov.name ov)
             | UVar uv => uvToDoc env uv
        and uvToDoc env uv =
            case TypeVars.Uv.get env uv
            of Either.Right t => concrToDoc env t
             | Either.Left uv => text "^" <> Name.toDoc (TypeVars.Uv.name env uv)

        structure Concr = struct
            open Concr

            datatype t = datatype concr

            val toDoc = concrToDoc
            fun toString env = Concr.toString (svarToDoc env)

            fun occurs env uv = FType.Concr.occurs (svarOccurs env) uv
            and svarOccurs env uv =
                fn Path path =>
                    (case TypeVars.Path.get env path
                     of Either.Left t => occurs env uv t
                      | Either.Right (uv', _) => uvOccurs env uv uv')
                 | OVar _ => false
                 | UVar uv' => uvOccurs env uv uv'
            and uvOccurs env uv uv' =
                case TypeVars.Uv.get env uv'
                of Either.Left uv' => TypeVars.Uv.eq (uv, uv')
                 | Either.Right t => occurs env uv t

            fun pathOccurs env path = FType.Concr.occurs (pathSvarOccurs env) path
            and pathSvarOccurs env path =
                fn Path path' => TypeVars.Path.eq (path', path)
                 | OVar _ => false
                 | UVar uv => (case TypeVars.Uv.get env uv
                               of Either.Left uv => false
                                | Either.Right t => pathOccurs env path t)

            fun substitute env kv = FType.Concr.substitute (svarSubstitute env) kv
            and svarSubstitute env kv =
                fn Path path =>
                    (case TypeVars.Path.get env path
                     of Either.Left _ => NONE (* path faces are always CallTFn:s with OVar args *)
                      | Either.Right (uv, _) => uvSubstitute env kv uv)
                 | OVar _ => NONE
                 | UVar uv => uvSubstitute env kv uv
            and uvSubstitute env kv uv =
                case TypeVars.Uv.get env uv
                of Either.Left _ => NONE
                 | Either.Right t => SOME (substitute env kv t)
        end

        structure Co = struct
            open Co

            fun toDoc env = Co.toDoc (svarToDoc env)
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

