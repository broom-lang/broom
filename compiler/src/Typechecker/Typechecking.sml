signature TYPECHECKING = sig
    structure ScopeId: ID
   
    datatype sv = UVar of uv
    withtype concr = sv FAst.Type.concr
    and abs = sv FAst.Type.abs
    and uv = (ScopeId.t, sv FAst.Type.concr) TypeVars.uv

    val svarToDoc: sv -> PPrint.t

    structure Type: sig
        val concrToDoc: concr -> PPrint.t
        val concrToString: concr -> string
        val absToDoc: abs -> PPrint.t
        val absToString: abs -> string
        val substitute: Id.t * concr -> concr -> concr
        val absSubstitute: Id.t * concr -> abs -> abs
    end

    val concrOccurs: uv -> concr -> bool
    val absOccurs: uv -> abs -> bool
end

structure TypecheckingCst :> TYPECHECKING = struct
    structure ScopeId :> ID = Id

    val text = PPrint.text
    val op<> = PPrint.<>

    datatype sv = UVar of uv
    withtype concr = sv FAst.Type.concr
    and abs = sv FAst.Type.abs
    and uv = (ScopeId.t, sv FAst.Type.concr) TypeVars.uv

    val rec svarToDoc =
        fn UVar uv => (case TypeVars.uvGet uv
                       of Either.Right t => FAst.Type.Concr.toDoc svarToDoc t
                        | Either.Left uv => text "^" <> Name.toDoc (TypeVars.uvName uv))
   
    structure Type = struct
        val concrToDoc = FAst.Type.Concr.toDoc svarToDoc
        val concrToString = FAst.Type.Concr.toString svarToDoc
        val absToDoc = FAst.Type.Abs.toDoc svarToDoc
        val absToString = FAst.Type.Abs.toString svarToDoc

        fun substitute kv = FAst.Type.Concr.substitute svarSubstitute kv

        and absSubstitute kv = FAst.Type.Abs.substitute svarSubstitute kv

        and svarSubstitute kv =
            fn UVar uv => (case TypeVars.uvGet uv
                           of Either.Left _ => NONE
                            | Either.Right t => SOME (substitute kv t))
    end

    fun concrOccurs uv = FAst.Type.Concr.occurs svarOccurs uv
    and absOccurs uv = FAst.Type.Abs.occurs svarOccurs uv
    and svarOccurs uv =
        fn UVar uv' => (case TypeVars.uvGet uv'
                       of Either.Left uv' => TypeVars.uvEq (uv', uv)
                        | Either.Right t => concrOccurs uv t)
end

