structure Typechecker :> sig
    val elaborateExpr: TypecheckingCst.scope -> TypecheckingCst.expr ref -> TypecheckingCst.typ
end = struct
    structure CTerm = FixedCst.Term
    structure CType = FixedCst.Type
    structure TC = TypecheckingCst
    structure FTerm = FAst.Term
    structure FType = FAst.Type

    open TypeError
 
    val subType = Subtyping.subType

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
    fun lookupValType pos name scope: TC.typ option =
        let fun valBindingType scope {typ = typRef, value} =
                case !typRef
                of SOME typ => elabType scope typ
                 | NONE => (case value
                            of SOME expr => elaborateExpr scope expr
                             | NONE => TC.UVar (pos, TypeVars.freshUv scope))

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
                let val typ = TC.UVar (pos, TypeVars.freshUv scope)
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
                 | NONE => Option.mapPartial (lookupValType pos name) (!parent))
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
              | CType.Record (pos, row) => TC.OutputType (FType.Record (pos, elaborateType scope row))
              | CType.RowExt (pos, {field = (label, fieldt), ext}) =>
                 TC.OutputType (FType.RowExt (pos, { field = (label, elaborateType scope fieldt)
                                                   , ext = elaborateType scope ext }))
              | CType.EmptyRow pos => TC.OutputType (FType.EmptyRow pos)
              | CType.Path typExpr =>
                 (case elaborateExpr scope typExpr
                  of TC.OutputType typ =>
                      (case typ
                       of FType.Type (_, ref typ) => typ
                        | _ => raise Fail ("Type path does not denote type at "
                                           ^ Pos.toString (TC.Expr.pos (!typExpr)))))
              | CType.Prim (pos, p) => TC.OutputType (FType.Prim (pos, p)))
         | TC.OutputType _ => typ (* assumes invariant: entire subtree has been elaborated already *)

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
                 let val domain = ref (case lookupValType pos param scope
                                       of SOME domain => domain
                                        | NONE => raise TypeError (UnboundVal (pos, param)))
                     val codomain = ref (TC.UVar (pos, TypeVars.freshUv (valOf (TC.Scope.parent scope))))
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
              | CTerm.Record (pos, fields) =>
                 let val (rowType, rowExpr) = elaborateFields scope pos fields
                     val typ = TC.OutputType (FType.Record (pos, ref rowType))
                 in exprRef := rowExpr
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
              | CTerm.Ann (_, expr, t) =>
                 ( elaborateExprAs scope (!(elaborateType scope t)) expr
                 ; !t )
              | CTerm.Type (pos, t) =>
                 let val t = elaborateType scope t
                 in exprRef := TC.OutputExpr (FTerm.Type (pos, t))
                  ; TC.OutputType (FType.Type (pos, t))
                 end
              | CTerm.Use (pos, name) =>
                 let val typ = case lookupValType pos name scope
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

    and elaborateFields scope pos (fields: TC.expr ref CTerm.row): TC.typ * TC.expr =
        let fun elaborateField (field as (label, expr), (rowType, fieldExprs)) =
                let val pos = TC.Expr.pos (!expr)
                    val fieldt = elaborateExpr scope expr
                in ( FType.RowExt (pos, {field = (label, ref fieldt), ext = TC.wrapOT rowType})
                   , field :: fieldExprs )
                end
            val (rowType, fieldExprs) = Vector.foldr elaborateField (FType.EmptyRow pos, []) fields
            val rowType = TC.OutputType rowType
        in (rowType, TC.OutputExpr (FTerm.Extend (pos, ref rowType, Vector.fromList fieldExprs, NONE)))
        end

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
                 | TC.UVar (_, uv) =>
                    (case TypeVars.uvGet uv
                     of Either.Left uv => raise Fail "unimplemented"
                      | Either.Right typ => coerce typ)
        in coerce typ
        end
   
    (* Coerce `expr` (in place) into a record with at least `label` and return the `label`:ed type. *)
    and coerceRecord scope (expr: TC.expr ref) (typ: TC.typ) label: TC.typ =
        let val rec coerce =
                fn TC.OutputType typ =>
                    (case typ
                     of FType.Record (_, row) => coerceRow (!row))
                 | TC.UVar (pos, uv) =>
                    (case TypeVars.uvGet uv
                     of Either.Right typ => coerce typ
                      | Either.Left uv => let val fieldType = TC.UVar (pos, TypeVars.freshUv scope)
                                              val ext = ref (TC.UVar (pos, TypeVars.freshUv scope))
                                              val pos = TC.Expr.pos (!expr)
                                              val row = FType.RowExt (pos, {field = (label, ref fieldType), ext})
                                              val typ = FType.Record (pos, ref (TC.OutputType row))
                                          in TypeVars.uvSet (uv, TC.OutputType typ)
                                           ; fieldType
                                          end)
            and coerceRow =
                fn TC.OutputType (FType.RowExt (_, {field = (label', fieldt), ext})) =>
                    if label' = label
                    then !fieldt
                    else coerceRow (!ext)
        in coerce typ
        end
end

