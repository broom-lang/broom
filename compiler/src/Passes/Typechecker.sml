structure Typechecker :> sig
    datatype type_error = UnCallable of TypecheckingCst.expr * TypecheckingCst.typ
                        | UnboundVal of Pos.t * Name.t
    exception TypeError of type_error

    val typeErrorToString: type_error -> string

    val elaborateExpr: TypecheckingCst.scope -> TypecheckingCst.expr ref -> TypecheckingCst.typ ref
   
    (* TODO: Finishing elaboration ('ejection'?) *)
end = struct
    structure CTerm = FixedCst.Term
    structure CType = FixedCst.Type
    structure TC = TypecheckingCst
    structure FTerm = FAst.Term
    structure FType = FAst.Type

    datatype type_error = UnCallable of TypecheckingCst.expr * TypecheckingCst.typ
                        | UnboundVal of Pos.t * Name.t
    exception TypeError of type_error

    fun typeErrorToString err =
        let val (pos, details) = case err
                                 of UnCallable (expr, typ) =>
                                     ( TC.exprPos expr
                                     , "Value " ^ TC.exprToString expr
                                           ^ " of type " ^ TC.typeToString typ ^ " can not be called" )
                                  | UnboundVal (pos, name) => (pos, "Unbound variable " ^ Name.toString name)
        in "TypeError in " ^ Pos.toString pos ^ ": " ^ details
        end

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    fun assign scope (y, uv, t) =
        let fun doAssign (uv, typRef) =
                case !typRef
                of TC.InputType _ => raise Fail "unreachable"
                 | TC.OutputType t =>
                    (case t
                     of FType.Arrow (pos, {domain, codomain}) =>
                         let val domainUv = TypeVars.freshUv scope
                             val codomainUv = TypeVars.freshUv scope
                             val t' = FType.Arrow (pos, { domain = ref (TC.UVar domainUv)
                                                        , codomain = ref (TC.UVar codomainUv)})
                         in TypeVars.uvSet (uv, ref (TC.OutputType t'))
                          ; assign scope (flipY y, domainUv, domain)
                          ; assign scope (y, codomainUv, codomain)
                         end
                      | FType.Prim _ => TypeVars.uvSet (uv, typRef))
                 | TC.UVar uv' => (case TypeVars.uvGet uv'
                                   of Either.Left uv' => TC.uvMerge (uv, uv')
                                    | Either.Right t => doAssign (uv, t))
                 | TC.OVar _ => TypeVars.uvSet (uv, typRef)
        in if TC.uvInScope (scope, uv)
           then if TC.occurs uv t
                then raise Fail "Occurs check"
                else doAssign (uv, t)
           else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv))
        end

    fun subType scope (typRef, superTypRef) =
        case (!typRef, !superTypRef)
        of (TC.OutputType t, TC.OutputType t') =>
            (case (t, t')
             of (FType.Prim (_, pl), FType.Prim (_, pr)) =>
                 if pl = pr
                 then NONE
                 else raise Fail "<:")
         | (TC.UVar uv, TC.UVar uv') =>
            (case (TypeVars.uvGet uv, TypeVars.uvGet uv')
             of (Either.Left uv, Either.Left uv') =>
                 if TC.uvInScope (scope, uv)
                 then if TC.uvInScope (scope, uv')
                      then if TypeVars.uvEq (uv, uv')
                           then NONE
                           else ( TC.uvMerge (uv, uv'); NONE )
                      else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv'))
                 else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv'))
              | (Either.Left uv, Either.Right t) => ( assign scope (Sub, uv, t); NONE )
              | (Either.Right t, Either.Left uv) => ( assign scope (Super, uv, t); NONE )
              | (Either.Right t, Either.Right t') => subType scope (t, t'))
         | (TC.UVar uv, _) =>
            (case TypeVars.uvGet uv
             of Either.Left uv => ( assign scope (Sub, uv, superTypRef); NONE )
              | Either.Right t => subType scope (t, superTypRef))
         | (_, TC.UVar uv) =>
            (case TypeVars.uvGet uv
             of Either.Left uv => ( assign scope (Super, uv, typRef); NONE )
              | Either.Right t => subType scope (typRef, t))

    local
        fun unfixExpr exprRef =
            case !exprRef
            of TC.OutputExpr expr => expr
             | TC.ScopeExpr {expr, ...} => unfixExpr expr
             | TC.InputExpr _ => raise Fail "unfix encountered InputExpr"
    in
        val fExprType = FTerm.typeOf (ref o TC.OutputType) unfixExpr
    end

    fun valShadeRef pos name =
        fn TC.ExprScope {vals, parent, ...} =>
            (case NameHashTable.find vals name
             of SOME {shade, ...} => shade
              | NONE =>
                 (case Option.map (valShadeRef pos name) (!parent)
                  of SOME shade => shade
                   | NONE => raise TypeError (UnboundVal (pos, name))))

    fun lookupType name scope =
        case scope
        of TC.ExprScope {vals, parent, ...} =>
            (case NameHashTable.find vals name
             of SOME {shade, binder} =>
                 (case !shade
                  of TC.Black => SOME (ref (valOf (!(#typ binder))))
                   | TC.White =>
                      (case !(#typ binder)
                       of SOME typ => SOME (elaborateValType scope name (ref typ)))
                   | TC.Grey =>
                      raise Fail ("lookupType cycle at " ^ Name.toString name))
              | NONE => Option.mapPartial (lookupType name) (!parent))

    and elaborateType scope typRef =
        let val typ = case !typRef 
                      of TC.InputType (CType.Arrow (pos, {domain, codomain})) =>
                          FType.Arrow (pos, { domain = elaborateType scope domain
                                            , codomain = elaborateType scope codomain })
                       | TC.InputType (CType.Prim (pos, p)) => FType.Prim (pos, p)
        in typRef := TC.OutputType typ
         ; typRef
        end

    and elaborateValType scope name typRef =
        case !typRef
        of TC.InputType typ =>
            let val pos = CType.pos typ
            in valShadeRef pos name scope := TC.Grey
             ; elaborateType scope typRef
             ; valShadeRef pos name scope := TC.Black
             ; typRef
            end
         | TC.ScopeType (scope as {typ, ...}) => elaborateValType (TC.TypeScope scope) name typ
         | TC.OutputType _ | TC.OVar _ | TC.UVar _ => typRef

    fun elaborateExpr scope exprRef =
        case !exprRef
        of TC.InputExpr expr =>
            (case expr
             of CTerm.Fn (pos, param, _, body) =>
                 let val domain = case lookupType param scope
                                  of SOME domain => domain
                                   | NONE => raise TypeError (UnboundVal (pos, param))
                     val codomain = ref (TC.UVar (TypeVars.freshUv (valOf (TC.scopeParent scope))))
                 in elaborateExprAs scope codomain body
                  ; exprRef := TC.OutputExpr (FTerm.Fn (pos, {var = param, typ = domain}, body))
                  ; ref (TC.OutputType (FType.Arrow (pos, {domain, codomain})))
                 end
              | CTerm.Let (pos, stmts, body) =>
                 let val stmts = Vector.map (elaborateStmt scope) stmts
                     val typ = elaborateExpr scope body
                 in exprRef := TC.OutputExpr (FTerm.Let (pos, stmts, body))
                  ; typ
                 end
              | CTerm.App (pos, {callee, arg}) =>
                 let val {domain, codomain} = coerceCallee callee (elaborateExpr scope callee)
                 in elaborateExprAs scope domain arg
                  ; exprRef := TC.OutputExpr (FTerm.App (pos, codomain, {callee, arg}))
                  ; codomain
                 end
              | CTerm.Ann (pos, expr, t) =>
                 ( elaborateExprAs scope (elaborateType scope t) expr
                 ; t )
              | CTerm.Use (pos, name) =>
                 let val typRef = case lookupType name scope
                                  of SOME typRef => typRef
                                   | NONE => raise TypeError (UnboundVal (pos, name))
                     val def = { var = name, typ = typRef }
                 in exprRef := TC.OutputExpr (FTerm.Use (pos, def))
                  ; typRef
                 end
              | CTerm.Const (pos, c) =>
                 ( exprRef := TC.OutputExpr (FTerm.Const (pos, c))
                 ; ref (TC.OutputType (FType.Prim (pos, Const.typeOf c))) ))
         | TC.ScopeExpr (scope as {expr, ...}) => elaborateExpr (TC.ExprScope scope) expr
         | TC.OutputExpr expr =>
            (* Assumes invariant: the whole subtree has been elaborated already. *)
            fExprType expr

    and elaborateExprAs scope typRef exprRef =
        case (!typRef, !exprRef)
        of (TC.OutputType t, TC.InputExpr expr) =>
            (case (t, expr)
             of (FType.ForAll _, expr) => raise Fail "unimplemented"
              | (FType.Arrow _, CTerm.Fn _) => raise Fail "unimplemented"
              | (_, _) =>
                 let val t' = elaborateExpr scope exprRef
                     val coercion = getOpt (subType scope (t', typRef), ignore)
                 in coercion exprRef
                 end)
         | (_, TC.ScopeExpr (scope as {expr, ...})) => ignore (elaborateExpr (TC.ExprScope scope) expr)
         | (_, TC.OutputExpr expr) =>
            (* Assumes invariant: the whole subtree has been elaborated already. *)
            ignore (fExprType expr)
         | (TC.OVar _ | TC.UVar _, TC.InputExpr _) =>
            let val t' = elaborateExpr scope exprRef
                val coercion = getOpt (subType scope (t', typRef), ignore)
            in coercion exprRef
            end

    and elaborateStmt scope =
        fn CTerm.Val (pos, name, SOME annTypeRef, exprRef) =>
            let val exprType = elaborateExpr scope exprRef
                val annType = elaborateValType scope name annTypeRef
                val coercion = getOpt (subType scope (exprType, annType), ignore)
            in coercion exprRef
             ; FTerm.Val (pos, {var = name, typ = annTypeRef}, exprRef)
            end
         | CTerm.Expr exprRef =>
            ( ignore (elaborateExpr scope exprRef)
            ; FTerm.Expr exprRef )

    and coerceCallee callee typRef =
        case !typRef
        of TC.InputType _ => raise Fail "unimplemented"
         | TC.ScopeType (scope as {typ, ...}) => raise Fail "unimplemented"
         | TC.OutputType typ =>
            (case typ
             of FType.ForAll _ => raise Fail "unimplemented"
              | FType.Arrow (_, domains) => domains
              | _ => raise TypeError (UnCallable (!callee, !typRef)))
         | TC.OVar _ => raise TypeError (UnCallable (!callee, !typRef))
         | TC.UVar uv =>
            (case TypeVars.uvGet uv
             of Either.Left uv => raise Fail "unimplemented"
              | Either.Right typ => coerceCallee callee typ)
end

