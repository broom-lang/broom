structure Typechecker :> sig
    datatype type_error = UnCallable of TypecheckingCst.expr * TypecheckingCst.typ
                        | UnboundVal of Pos.t * Name.t
                        | Occurs of (TypecheckingCst.scope, TypecheckingCst.typ) TypeVars.uv
                                  * TypecheckingCst.typ
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

    structure TypeError = struct
        datatype type_error = UnCallable of TypecheckingCst.expr * TypecheckingCst.typ
                            | UnboundVal of Pos.t * Name.t
                            | Occurs of (TypecheckingCst.scope, TypecheckingCst.typ) TypeVars.uv
                                      * TypecheckingCst.typ
        exception TypeError of type_error

        fun typeErrorToString err =
            let val (pos, details) = case err
                                     of UnCallable (expr, typ) =>
                                         ( TC.exprPos expr
                                         , "Value " ^ TC.exprToString expr
                                               ^ " of type " ^ TC.typeToString typ ^ " can not be called" )
                                      | UnboundVal (pos, name) => (pos, "Unbound variable " ^ Name.toString name)
                                      | Occurs (uv, t) =>
                                         ( TC.Type.pos t
                                         , "Occurs check: unifying " ^ Name.toString (TypeVars.uvName uv)
                                               ^ " with " ^ TC.typeToString t ^ " would create infinite type" )
            in "TypeError in " ^ Pos.toString pos ^ ": " ^ details
            end
    end
    open TypeError

(* Subtyping and UVar Assignment *)

    datatype lattice_y = Sub | Super

    val flipY = fn Sub => Super
                 | Super => Sub

    fun assign scope (y, uv: (TC.scope, TC.typ) TypeVars.uv, t: TC.typ): unit =
        let fun doAssign (uv, typ) =
                case typ
                of TC.InputType _ => raise Fail "unreachable"
                 | TC.OutputType t =>
                    (case t
                     of FType.Arrow (pos, {domain, codomain}) =>
                         let val domainUv = TypeVars.freshUv scope
                             val codomainUv = TypeVars.freshUv scope
                             val t' = FType.Arrow (pos, { domain = ref (TC.UVar domainUv)
                                                        , codomain = ref (TC.UVar codomainUv)})
                         in TypeVars.uvSet (uv, TC.OutputType t')
                          ; assign scope (flipY y, domainUv, !domain)
                          ; assign scope (y, codomainUv, !codomain)
                         end
                      | FType.Prim _ => TypeVars.uvSet (uv, typ))
                 | TC.UVar uv' => (case TypeVars.uvGet uv'
                                   of Either.Left uv' => TC.uvMerge (uv, uv')
                                    | Either.Right t => doAssign (uv, t))
                 | TC.OVar _ => TypeVars.uvSet (uv, typ)
        in if TC.uvInScope (scope, uv)
           then if TC.occurs uv t
                then raise TypeError (Occurs (uv, t))
                else doAssign (uv, t)
           else raise Fail ("Unification var out of scope: " ^ Name.toString (TypeVars.uvName uv))
        end

    fun subType scope (typ: TC.typ, superTyp: TC.typ): (TC.expr ref -> unit) option =
        case (typ, superTyp)
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
             of Either.Left uv => ( assign scope (Sub, uv, superTyp); NONE )
              | Either.Right t => subType scope (t, superTyp))
         | (_, TC.UVar uv) =>
            (case TypeVars.uvGet uv
             of Either.Left uv => ( assign scope (Super, uv, typ); NONE )
              | Either.Right t => subType scope (typ, t))

(* Hacky Utils *)

    local
        fun unfixExpr exprRef =
            case !exprRef
            of TC.OutputExpr expr => expr
             | TC.ScopeExpr {expr, ...} => unfixExpr expr
             | TC.InputExpr _ => raise Fail "unfix encountered InputExpr"
    in
        val fExprType = FTerm.typeOf (ref o TC.OutputType) unfixExpr
    end

(* Looking up `val` types *)

    fun valShadeRef pos name: TC.scope -> TC.shade ref =
        fn TC.ExprScope {vals, parent, ...} =>
            (case NameHashTable.find vals name
             of SOME {shade, ...} => shade
              | NONE =>
                 (case Option.map (valShadeRef pos name) (!parent)
                  of SOME shade => shade
                   | NONE => raise TypeError (UnboundVal (pos, name))))

    fun lookupValType pos name scope: TC.typ option =
        let fun valBindingType scope {typ = typRef, value} =
                case !typRef
                of SOME typ => elabType scope typ
                 | NONE => (case value
                            of SOME expr => !(elaborateExpr scope expr)
                             | NONE => TC.UVar (TypeVars.freshUv scope))
            fun elaborateValType scope (binding as {typ = typRef, value = _}) =
                let do valShadeRef pos name scope := TC.Grey
                    val typ = valBindingType scope binding
                    val shade = valShadeRef pos name scope
                in case !shade
                   of TC.Grey => ( typRef := SOME typ
                                 ; shade := TC.Black )
                    | TC.Black => let val typ' = valOf (!typRef)
                                  (* HACK?: mutual subtyping: *)
                                  in subType scope (typ, typ')
                                   ; subType scope (typ', typ)
                                   ; ()
                                  end
                    | TC.White => raise Fail "unreachable"
                 ; typ
                end
        in case scope
           of TC.ExprScope {vals, parent, ...} =>
               (case NameHashTable.find vals name
                of SOME {shade, binder} =>
                    (case !shade
                     of TC.Black => !(#typ binder)
                      | TC.White => SOME (elaborateValType scope binder)
                      | TC.Grey =>
                         let val typ = TC.UVar (TypeVars.freshUv scope)
                         in #typ binder := SOME typ
                          ; shade := TC.Black
                          ; SOME typ
                         end)
                 | NONE => Option.mapPartial (lookupValType pos name) (!parent))
        end

(* Elaborating subtrees *)

    and elabType scope (typ: TC.typ): TC.typ =
        case typ
        of TC.InputType (CType.Arrow (pos, {domain, codomain})) =>
            TC.OutputType (FType.Arrow (pos, { domain = elaborateType scope domain
                                             , codomain = elaborateType scope codomain }))
         | TC.InputType (CType.Prim (pos, p)) => TC.OutputType (FType.Prim (pos, p))

    and elaborateType scope (typRef: TC.typ ref): TC.typ ref =
        ( typRef := elabType scope (!typRef)
        ; typRef )

    and elaborateExpr scope (exprRef: TC.expr ref): TC.typ ref =
        case !exprRef
        of TC.InputExpr expr =>
            (case expr
             of CTerm.Fn (pos, param, _, body) =>
                 let val domain = ref (case lookupValType pos param scope
                                       of SOME domain => domain
                                        | NONE => raise TypeError (UnboundVal (pos, param)))
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
                 let val {domain, codomain} = coerceCallee callee (!(elaborateExpr scope callee))
                 in elaborateExprAs scope domain arg
                  ; exprRef := TC.OutputExpr (FTerm.App (pos, codomain, {callee, arg}))
                  ; codomain
                 end
              | CTerm.Ann (pos, expr, t) =>
                 ( elaborateExprAs scope (elaborateType scope t) expr
                 ; t )
              | CTerm.Use (pos, name) =>
                 let val typRef = ref (case lookupValType pos name scope
                                       of SOME typRef => typRef
                                        | NONE => raise TypeError (UnboundVal (pos, name)))
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

    and elaborateExprAs scope (typRef: TC.typ ref) (exprRef: TC.expr ref): unit =
        case (!typRef, !exprRef)
        of (TC.OutputType t, TC.InputExpr expr) =>
            (case (t, expr)
             of (FType.ForAll _, expr) => raise Fail "unimplemented"
              | (FType.Arrow _, CTerm.Fn _) => raise Fail "unimplemented"
              | (_, _) =>
                 let val t' = elaborateExpr scope exprRef
                     val coercion = getOpt (subType scope (!t', !typRef), ignore)
                 in coercion exprRef
                 end)
         | (_, TC.ScopeExpr (scope as {expr, ...})) => ignore (elaborateExpr (TC.ExprScope scope) expr)
         | (_, TC.OutputExpr expr) =>
            (* Assumes invariant: the whole subtree has been elaborated already. *)
            ignore (fExprType expr)
         | (TC.OVar _ | TC.UVar _, TC.InputExpr _) =>
            let val t' = elaborateExpr scope exprRef
                val coercion = getOpt (subType scope (!t', !typRef), ignore)
            in coercion exprRef
            end

    and elaborateStmt scope =
        fn CTerm.Val (pos, name, oannTypeRef, exprRef) =>
            let val exprType = !(elaborateExpr scope exprRef)
                val annType = valOf (lookupValType pos name scope)
                val annTypeRef = case oannTypeRef
                                 of SOME annTypeRef => (annTypeRef := annType; annTypeRef)
                                  | NONE => ref annType
                val coercion = getOpt (subType scope (exprType, annType), ignore)
            in coercion exprRef
             ; FTerm.Val (pos, {var = name, typ = annTypeRef}, exprRef)
            end
         | CTerm.Expr exprRef =>
            ( ignore (elaborateExpr scope exprRef)
            ; FTerm.Expr exprRef )

    and coerceCallee (callee: TC.expr ref) (typ: TC.typ): {domain: TC.typ ref, codomain: TC.typ ref} =
        let val rec coerce =
                fn TC.InputType _ => raise Fail "unimplemented"
                 | TC.ScopeType (scope as {typ, ...}) => raise Fail "unimplemented"
                 | TC.OutputType otyp =>
                    (case otyp
                     of FType.ForAll _ => raise Fail "unimplemented"
                      | FType.Arrow (_, domains) => domains
                      | _ => raise TypeError (UnCallable (!callee, typ)))
                 | TC.OVar _ => raise TypeError (UnCallable (!callee, typ))
                 | TC.UVar uv =>
                    (case TypeVars.uvGet uv
                     of Either.Left uv => raise Fail "unimplemented"
                      | Either.Right typ => coerce typ)
        in coerce typ
        end
end

