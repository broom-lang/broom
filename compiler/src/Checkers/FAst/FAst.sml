structure FAst = struct
    structure ScopeId = ScopeId

    val text = PPrint.text
    val op<> = PPrint.<>

    structure Type = struct
        open FTypeBase
        structure ScopeId = ScopeId

        datatype concr' = datatype FTypeBase.concr
        datatype co' = datatype FTypeBase.co

        datatype sv = UVar of uv | Path of path
        withtype concr = sv FTypeBase.concr
        and co = sv FTypeBase.co
        and uv = sv FTypeBase.concr TypeVars.uv
        and path = sv FTypeBase.concr TypeVars.path

        type ('expr, 'error) env = (concr, 'expr, 'error) TypecheckingEnv.t

        fun concrToDoc env = fn t => FTypeBase.Concr.toDoc (svarToDoc env) t
        and svarToDoc env =
            fn Path path =>
                (case TypeVars.Path.get env path
                 of Either.Right (uv, _) => uvToDoc env uv
                  | Either.Left t => text "^^" <> PPrint.parens (concrToDoc env t))
             | UVar uv => uvToDoc env uv
        and uvToDoc env uv =
            case TypeVars.Uv.get env uv
            of Either.Right t => concrToDoc env t
             | Either.Left uv => text "^" <> Name.toDoc (TypeVars.Uv.name env uv)

        structure Concr = struct
            open Concr

            type t = concr

            val toDoc = concrToDoc
            fun toString env = Concr.toString (svarToDoc env)

            fun occurs env uv = FTypeBase.Concr.occurs (svarOccurs env) uv
            and svarOccurs env uv =
                fn Path path =>
                    (case TypeVars.Path.get env path
                     of Either.Left t => occurs env uv t
                      | Either.Right (uv', _) => uvOccurs env uv uv')
                 | UVar uv' => uvOccurs env uv uv'
            and uvOccurs env uv uv' =
                case TypeVars.Uv.get env uv'
                of Either.Left uv' => TypeVars.Uv.eq (uv, uv')
                 | Either.Right t => occurs env uv t

            fun substitute env kv = FTypeBase.Concr.substitute (svarSubstitute env) kv
            and svarSubstitute env kv =
                fn Path path =>
                    (case TypeVars.Path.get env path
                     of Either.Left _ => NONE (* FIXME? *)
                      | Either.Right (uv, _) => uvSubstitute env kv uv)
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

