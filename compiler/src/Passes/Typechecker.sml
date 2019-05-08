structure Typechecker :> sig
    datatype type_error = UnCallable of TypecheckingCst.expr * TypecheckingCst.typ
                        | UnboundVal of Pos.t * Name.t
                        | Occurs of (TypecheckingCst.scope, TypecheckingCst.typ) TypeVars.uv
                                  * TypecheckingCst.typ
    exception TypeError of type_error

    val typeErrorToString: type_error -> string

    val elaborateExpr: TypecheckingCst.scope -> TypecheckingCst.expr ref -> TypecheckingCst.typ
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

    (* Assign the unification variable `uv` to a sub/supertype (`y`) of `t` *)
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

    (* Check that `typ` <: `superTyp` and return the (mutating) coercion if any. *)
    fun subType scope (typ: TC.typ, superTyp: TC.typ): (TC.expr ref -> unit) option =
        case (typ, superTyp)
        of (TC.OutputType t, TC.OutputType t') =>
            (case (t, t')
             of (FType.Arrow (_, arr), FType.Arrow (_, arr')) => subArrows scope (arr, arr')
              | (FType.Prim (_, pl), FType.Prim (_, pr)) =>
                 if pl = pr
                 then NONE
                 else raise Fail "<:"
              | (FType.Type (pos, tref as ref t), FType.Type (_, ref t')) =>
                 ( subType scope (t, t')
                 ; subType scope (t', t)
                 ; SOME (fn expr => expr := TC.OutputExpr (FTerm.Type (pos, tref)))))
         | (TC.UVar uv, TC.UVar uv') => subUvs scope (uv, uv')
         | (TC.UVar uv, _) =>
            (case TypeVars.uvGet uv
             of Either.Left uv => ( assign scope (Sub, uv, superTyp); NONE )
              | Either.Right t => subType scope (t, superTyp))
         | (_, TC.UVar uv) =>
            (case TypeVars.uvGet uv
             of Either.Left uv => ( assign scope (Super, uv, typ); NONE )
              | Either.Right t => subType scope (typ, t))

    and subArrows scope ({domain, codomain}, {domain = domain', codomain = codomain'}) =
        let val coerceDomain = subType scope (!domain', !domain)
            val coerceCodomain = subType scope (!codomain, !codomain')
        in if isSome coerceDomain orelse isSome coerceCodomain
           then let val coerceDomain = getOpt (coerceDomain, fn _ => ())
                    val coerceCodomain = getOpt (coerceCodomain, fn _ => ())
                in SOME (fn expr =>
                             let val pos = TC.exprPos (!expr)
                                 val param = {var = Name.fresh (), typ = domain'}
                                 val arg = ref (TC.OutputExpr (FTerm.Use (pos, param)))
                                 val callee = expr
                                 do coerceDomain arg
                                 val body = ref (TC.OutputExpr (FTerm.App (pos, codomain, {callee, arg})))
                                 do coerceCodomain body
                                 val expr' = FTerm.Fn (pos, param, body)
                             in expr := TC.OutputExpr expr'
                             end)
                end
           else NONE
        end

    and subUvs scope (uv: TC.uv, uv': TC.uv): (TC.expr ref -> unit) option =
        case (TypeVars.uvGet uv, TypeVars.uvGet uv')
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
         | (Either.Right t, Either.Right t') => subType scope (t, t')

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

    (* Get the type of the variable `name`, referenced at `pos`, from `scope` by either
       - finding the type annotation (if available) (and elaborating it if not already done)
       - elaborating the expression bound to the variable (if available)
       - returning a fresh unification variable (if neither type annotation nor bound expression
         is available or if a cycle is encountered) *)
    fun lookupValType name scope: TC.typ option =
        let fun valBindingType scope {typ = typRef, value} =
                case !typRef
                of SOME typ => elabType scope typ
                 | NONE => (case value
                            of SOME expr => elaborateExpr scope expr
                             | NONE => TC.UVar (TypeVars.freshUv scope))

            fun elaborateValType scope {shade, binder = binding as {typ = typRef, value = _}} =
                let do shade := TC.Grey
                    val typ = valBindingType scope binding
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

            fun elaborateValTypeLoop scope {shade, binder = {typ = typRef, value = _}} =
                let val typ = TC.UVar (TypeVars.freshUv scope)
                in typRef := SOME typ
                 ; shade := TC.Black
                 ; typ
                end
        in case scope
           of TC.ExprScope {vals, parent, ...} =>
               (case NameHashTable.find vals name
                of SOME (binding as {shade, binder}) =>
                    (case !shade
                     of TC.Black => !(#typ binder)
                      | TC.White => SOME (elaborateValType scope binding)
                      | TC.Grey => SOME (elaborateValTypeLoop scope binding))
                 | NONE => Option.mapPartial (lookupValType name) (!parent))
        end

(* Elaborating subtrees *)

    (* Elaborate the type `typ` and return the elaborated version. *)
    and elabType scope (typ: TC.typ): TC.typ =
        case typ
        of TC.InputType typ =>
            (case typ
             of CType.Arrow (pos, {domain, codomain}) =>
                 TC.OutputType (FType.Arrow (pos, { domain = elaborateType scope domain
                                                  , codomain = elaborateType scope codomain }))
              | CType.Path typExpr =>
                 (case elaborateExpr scope typExpr
                  of TC.OutputType typ =>
                      (case typ
                       of FType.Type (pos, ref typ) => typ
                        | _ => raise Fail ("Type path does not denote type at "
                                           ^ Pos.toString (TC.exprPos (!typExpr)))))
              | CType.Prim (pos, p) => TC.OutputType (FType.Prim (pos, p)))

    (* Like `elabType` but takes a ref, assigns to it and returns it for convenience. *)
    and elaborateType scope (typRef: TC.typ ref): TC.typ ref =
        ( typRef := elabType scope (!typRef)
        ; typRef )

    (* Elaborate the expression `exprRef` and return its computed type. *)
    and elaborateExpr scope (exprRef: TC.expr ref): TC.typ =
        case !exprRef
        of TC.InputExpr expr =>
            (case expr
             of CTerm.Fn (pos, param, _, body) =>
                 let val domain = ref (case lookupValType param scope
                                       of SOME domain => domain
                                        | NONE => raise TypeError (UnboundVal (pos, param)))
                     val codomain = ref (TC.UVar (TypeVars.freshUv (valOf (TC.Scope.parent scope))))
                 in elaborateExprAs scope (!codomain) body
                  ; exprRef := TC.OutputExpr (FTerm.Fn (pos, {var = param, typ = domain}, body))
                  ; TC.OutputType (FType.Arrow (pos, {domain, codomain}))
                 end
              | CTerm.Let (pos, stmts, body) =>
                 let val stmts = Vector.map (elaborateStmt scope) stmts
                     val typ = elaborateExpr scope body
                 in exprRef := TC.OutputExpr (FTerm.Let (pos, stmts, body))
                  ; typ
                 end
              | CTerm.App (pos, {callee, arg}) =>
                 let val {domain, codomain} = coerceCallee callee (elaborateExpr scope callee)
                 in elaborateExprAs scope (!domain) arg
                  ; exprRef := TC.OutputExpr (FTerm.App (pos, codomain, {callee, arg}))
                  ; !codomain
                 end
              | CTerm.Field (pos, expr, label) =>
                 let val fieldType = coerceRecord scope expr (elaborateExpr scope expr) label
                 in exprRef := TC.OutputExpr (FTerm.Field (pos, ref fieldType, expr, label))
                  ; fieldType
                 end
              | CTerm.Ann (pos, expr, t) =>
                 ( elaborateExprAs scope (!(elaborateType scope t)) expr
                 ; !t )
              | CTerm.Type (pos, t) =>
                 let val t = elaborateType scope t
                 in exprRef := TC.OutputExpr (FTerm.Type (pos, t))
                  ; TC.OutputType (FType.Type (pos, t))
                 end
              | CTerm.Use (pos, name) =>
                 let val typ = case lookupValType name scope
                               of SOME typRef => typRef
                                | NONE => raise TypeError (UnboundVal (pos, name))
                     val def = { var = name, typ = ref typ }
                 in exprRef := TC.OutputExpr (FTerm.Use (pos, def))
                  ; typ
                 end
              | CTerm.Const (pos, c) =>
                 ( exprRef := TC.OutputExpr (FTerm.Const (pos, c))
                 ; TC.OutputType (FType.Prim (pos, Const.typeOf c))) )
         | TC.ScopeExpr (scope as {expr, ...}) => elaborateExpr (TC.ExprScope scope) expr
         | TC.OutputExpr expr =>
            (* Assumes invariant: the whole subtree has been elaborated already. *)
            !(fExprType expr)

    (* Elaborate the expression `exprRef` to a subtype of `typ`. *)
    and elaborateExprAs scope (typ: TC.typ) (exprRef: TC.expr ref): unit =
        case (typ, !exprRef)
        of (TC.OutputType t, TC.InputExpr expr) =>
            (case (t, expr)
             of (FType.ForAll _, expr) => raise Fail "unimplemented"
              | (FType.Arrow _, CTerm.Fn _) => raise Fail "unimplemented"
              | (_, _) =>
                 let val t' = elaborateExpr scope exprRef
                     val coercion = getOpt (subType scope (t', typ), ignore)
                 in coercion exprRef
                 end)
         | (_, TC.ScopeExpr (scope as {expr, ...})) => ignore (elaborateExpr (TC.ExprScope scope) expr)
         | (_, TC.OutputExpr expr) =>
            (* Assumes invariant: the whole subtree has been elaborated already. *)
            ignore (fExprType expr)
         | (TC.OVar _ | TC.UVar _, TC.InputExpr _) =>
            let val t' = elaborateExpr scope exprRef
                val coercion = getOpt (subType scope (t', typ), ignore)
            in coercion exprRef
            end

    (* Elaborate a statement and return the elaborated version. *)
    and elaborateStmt scope: (TC.typ ref, TC.expr ref) Cst.Term.stmt -> (TC.typ ref, TC.expr ref) FTerm.stmt =
        fn CTerm.Val (pos, name, oannTypeRef, exprRef) =>
            let val exprType = elaborateExpr scope exprRef
                val annType = valOf (lookupValType name scope)
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

    (* Coerce `callee` into a function (in place) and return its `domain` and `codomain`. *)
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
   
    (* Coerce `expr` (in place) into a record with at least `label` and return the `label`:ed type. *)
    and coerceRecord scope (expr: TC.expr ref) (typ: TC.typ) label: TC.typ =
        let val rec coerce =
                fn TC.UVar uv =>
                    (case TypeVars.uvGet uv
                     of Either.Right typ => coerce typ
                      | Either.Left uv => let val fieldType = TC.UVar (TypeVars.freshUv scope)
                                              val ext = ref (TC.UVar (TypeVars.freshUv scope))
                                              val row = FType.RowExt {field = (label, ref fieldType), ext}
                                              val typ = FType.Record (TC.exprPos (!expr), row)
                                          in TypeVars.uvSet (uv, TC.OutputType typ)
                                           ; fieldType
                                          end)
        in coerce typ
        end
end

