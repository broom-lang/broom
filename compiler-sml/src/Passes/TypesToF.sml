structure TypesToF :> sig
    val programTypesToF: SemiFAst.Term.stmt vector -> FAst.Term.stmt vector
end = struct
    structure SFTerm = SemiFAst.Term
    structure FTerm = FAst.Term
    structure FType = FAst.Type

    fun typeDefTypesToF name = {name, kind = FType.TypeK}

    val rec typeToF =
        fn Type.ForAll (pos, def, body) =>
            FType.ForAll (pos, typeDefTypesToF def, typeToF body)
         | Type.UseT (pos, def) => FType.UseT (pos, typeDefTypesToF def)
         | Type.OVar (pos, ov) =>
           (* OVar existed just for Type.UseT scoping in Typecheck so it becomes a FType.UseT: *)
            FType.UseT (pos, typeDefTypesToF (TypeVars.ovName ov))
         | Type.UVar (pos, uv) =>
            (case TypeVars.uvGet uv
             of Either.Left uv => FType.Prim (pos, Type.Int) (* Unconstrained, so anything goes. *)
              | Either.Right t => typeToF t)
         | Type.Arrow (pos, {domain, codomain}) =>
            FType.Arrow (pos, {domain = typeToF domain, codomain = typeToF codomain})
         | Type.Prim (pos, p) => FType.Prim (pos, p)

    fun defTypesToF {name, typ} = {name, typ = typeToF typ}

    val rec exprTypesToF =
        fn SFTerm.Fn (pos, def, body) => FTerm.Fn (pos, defTypesToF def, exprTypesToF body)
         | SFTerm.TFn (pos, def, body) => FTerm.TFn (pos, typeDefTypesToF def, exprTypesToF body)
         | SFTerm.App (pos, {callee, arg}) =>
            FTerm.App (pos, {callee = exprTypesToF callee, arg = exprTypesToF arg})
         | SFTerm.TApp (pos, {callee, arg}) =>
            FTerm.TApp (pos, {callee = exprTypesToF callee, arg = typeToF arg})
         | SFTerm.Use (pos, def) => FTerm.Use (pos, defTypesToF def)
         | SFTerm.Const (pos, c) => FTerm.Const (pos, c)

    val stmtTypesToF =
        fn SFTerm.Def (pos, def, expr) => FTerm.Def (pos, defTypesToF def, exprTypesToF expr)

    fun programTypesToF stmts =
        Vector.map stmtTypesToF stmts
end