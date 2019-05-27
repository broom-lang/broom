structure Typechecker :> sig
    val elaborateExpr: TypecheckingCst.scope -> TypecheckingCst.expr
                     -> TypecheckingCst.typ * TypecheckingCst.typ FAst.Term.expr
end = struct
    structure CTerm = FixedCst.Term
    structure CType = FixedCst.Type
    structure TC = TypecheckingCst
    structure FTerm = FAst.Term
    structure FType = FAst.Type

    open TypeError
 
    val subType = Subtyping.subType
    val applyCoercion = Subtyping.applyCoercion

(* Looking up `val` types *)

    (* Get the type of the variable `name`, referenced at `pos`, from `scope` by either
       - finding the type annotation (if available) (and elaborating it if not already done)
       - elaborating the expression bound to the variable (if available)
       - returning a fresh unification variable (if neither type annotation nor bound expression
         is available or if a cycle is encountered) *)
    fun lookupValType pos name scope: TC.typ option =
        let fun valBindingType scope {typ = typRef, value} =
                case !typRef
                of SOME typ => elaborateType scope typ
                 | NONE => (case value
                            of SOME (ref expr) => #1 (elaborateExpr scope expr)
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
    and elaborateType scope (typ: TC.typ): TC.typ =
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
                 (case #1 (elaborateExpr scope typExpr)
                  of TC.OutputType typ =>
                      (case typ
                       of FType.Type (_, typ) => typ
                        | _ => raise Fail ("Type path does not denote type at "
                                           ^ Pos.toString (TC.Expr.pos typExpr))))
              | CType.Prim (pos, p) => TC.OutputType (FType.Prim (pos, p)))
         | TC.OutputType _ => typ (* assumes invariant: entire subtree has been elaborated already *)

    (* Elaborate the expression `exprRef` and return its computed type. *)
    and elaborateExpr scope (exprRef: TC.expr): TC.typ * TC.typ FTerm.expr =
        case exprRef
        of TC.InputExpr expr =>
            (case expr
             of CTerm.Fn (pos, param, _, body) =>
                 let val domain = case lookupValType pos param scope
                                  of SOME domain => domain
                                   | NONE => raise TypeError (UnboundVal (pos, param))
                     val codomain = TC.UVar (pos, TypeVars.freshUv (valOf (TC.Scope.parent scope)))
                     val body = elaborateExprAs scope codomain body
                 in ( TC.OutputType (FType.Arrow (pos, {domain, codomain}))
                    , FTerm.Fn (pos, {var = param, typ = domain}, body) )
                 end
              | CTerm.Let (pos, stmts, body) =>
                 let val stmts = Vector.map (elaborateStmt scope) stmts
                     val (typ, body) = elaborateExpr scope body
                 in (typ, FTerm.Let (pos, stmts, body))
                 end
              | CTerm.Record (pos, fields) =>
                 let val (rowType, rowExpr) = elaborateRowExpr scope pos fields
                     val typ = TC.OutputType (FType.Record (pos, rowType))
                 in (typ, rowExpr)
                 end
              | CTerm.App (pos, {callee, arg}) =>
                 let val ct as (_, callee) = elaborateExpr scope callee
                     val {domain, codomain} = coerceCallee ct 
                     val arg = elaborateExprAs scope domain arg
                 in (codomain, FTerm.App (pos, codomain, {callee, arg}))
                 end
              | CTerm.Field (pos, expr, label) =>
                 let val te as (_, expr) = elaborateExpr scope expr
                     val fieldType = coerceRecord scope te label
                 in (fieldType, FTerm.Field (pos, fieldType, expr, label))
                 end
              | CTerm.Ann (_, expr, t) =>
                 let val t = elaborateType scope t
                 in (t, elaborateExprAs scope t expr)
                 end
              | CTerm.Type (pos, t) =>
                 let val t = elaborateType scope t
                 in (TC.OutputType (FType.Type (pos, t)), FTerm.Type (pos, t))
                 end
              | CTerm.Use (pos, name) =>
                 let val typ = case lookupValType pos name scope
                               of SOME typ => typ
                                | NONE => raise TypeError (UnboundVal (pos, name))
                     val def = {var = name, typ}
                 in (typ, FTerm.Use (pos, def))
                 end
              | CTerm.Const (pos, c) =>
                 (TC.OutputType (FType.Prim (pos, Const.typeOf c)), FTerm.Const (pos, c)))
         | TC.ScopeExpr (scope as {expr, ...}) => elaborateExpr (TC.ExprScope scope) expr
         | TC.OutputExpr expr => (FTerm.typeOf TC.OutputType expr, expr)

    and elaborateRowExpr scope pos ({fields, ext}: TC.expr CTerm.row): TC.typ * TC.typ FTerm.expr =
        let fun elaborateField (field as (label, expr), (rowType, fieldExprs)) =
                let val pos = TC.Expr.pos expr
                    val (fieldt, expr) = elaborateExpr scope expr
                in ( TC.OutputType (FType.RowExt (pos, {field = (label, fieldt), ext = rowType}))
                   , (label, expr) :: fieldExprs )
                end
            val (extType, extExpr) = case ext
                                     of SOME ext => let val (t, ext) = elaborateExpr scope ext
                                                    in (t, SOME ext)
                                                    end
                                      | NONE => (TC.OutputType (FType.EmptyRow pos), NONE)
            val (rowType, fieldExprs) = Vector.foldr elaborateField (extType, []) fields
        in (rowType, FTerm.Extend (pos, rowType, Vector.fromList fieldExprs, extExpr))
        end

    (* Elaborate the expression `exprRef` to a subtype of `typ`. *)
    and elaborateExprAs scope (typ: TC.typ) (expr: TC.expr): TC.typ FTerm.expr =
        case (typ, expr)
        of (TC.OutputType t, TC.InputExpr iexpr) =>
            (case (t, iexpr)
             of (FType.ForAll _, expr) => raise Fail "unimplemented"
              | (FType.Arrow _, CTerm.Fn _) => raise Fail "unimplemented"
              | (_, _) =>
                 let val (t', expr) = elaborateExpr scope expr
                     val coercion = subType scope (t', typ)
                 in applyCoercion coercion expr
                 end)
         | (TC.OVar _ | TC.UVar _, TC.InputExpr _) =>
            let val (t', expr) = elaborateExpr scope expr
                val coercion = subType scope (t', typ)
            in applyCoercion coercion expr
            end
         | (_, TC.ScopeExpr (scope as {expr, ...})) => elaborateExprAs (TC.ExprScope scope) typ expr
         | (_, TC.OutputExpr expr) => expr
         | (TC.InputType _, _) => raise Fail "Encountered InputType"

    (* Elaborate a statement and return the elaborated version. *)
    and elaborateStmt scope: (TC.typ, TC.typ option ref, TC.expr, TC.expr ref) Cst.Term.stmt -> TC.typ FTerm.stmt =
        fn CTerm.Val (pos, name, _, exprRef) =>
            let val t = valOf (lookupValType pos name scope) (* `name` is in `scope` by construction *)
                val expr = elaborateExprAs scope t (!exprRef)
            in FTerm.Val (pos, {var = name, typ = t}, expr)
            end
         | CTerm.Expr expr => FTerm.Expr (elaborateExprAs scope (TC.OutputType (FType.unit (TC.Expr.pos expr))) expr)

    (* Coerce `callee` into a function (in place) and return its `domain` and `codomain`. *)
    and coerceCallee (typ: TC.typ, callee: TC.typ FTerm.expr): {domain: TC.typ, codomain: TC.typ} =
        let val rec coerce =
                fn TC.OutputType otyp =>
                    (case otyp
                     of FType.ForAll _ => raise Fail "unimplemented"
                      | FType.Arrow (_, domains) => domains
                      | _ => raise TypeError (UnCallable (callee, typ)))
                 | TC.OVar _ => raise TypeError (UnCallable (callee, typ))
                 | TC.UVar (_, uv) =>
                    (case TypeVars.uvGet uv
                     of Either.Left uv => raise Fail "unimplemented"
                      | Either.Right typ => coerce typ)
                 | TC.ScopeType (scope as {typ, ...}) => raise Fail "unimplemented"
                 | TC.InputType _ => raise Fail "Encountered InputType"
        in coerce typ
        end
   
    (* Coerce `expr` (in place) into a record with at least `label` and return the `label`:ed type. *)
    and coerceRecord scope (typ: TC.typ, expr: TC.typ FTerm.expr) label: TC.typ =
        let val rec coerce =
                fn TC.OutputType otyp =>
                    (case otyp
                     of FType.ForAll _ => raise Fail "unimplemented"
                      | FType.Record (_, row) => coerceRow row
                      | _ => raise TypeError (UnCallable (expr, typ)))
                 | TC.OVar _ => raise TypeError (UnDottable (expr, typ))
                 | TC.UVar (pos, uv) =>
                    (case TypeVars.uvGet uv
                     of Either.Right typ => coerce typ
                      | Either.Left uv => let val fieldType = TC.UVar (pos, TypeVars.freshUv scope)
                                              val ext = TC.UVar (pos, TypeVars.freshUv scope)
                                              val pos = FTerm.exprPos expr
                                              val row = FType.RowExt (pos, {field = (label, fieldType), ext})
                                              val typ = FType.Record (pos, TC.OutputType row)
                                          in TypeVars.uvSet (uv, TC.OutputType typ)
                                           ; fieldType
                                          end)
                 | TC.ScopeType _ => raise Fail "unimplemented"
                 | TC.InputType _ => raise Fail "Encountered InputType"
            and coerceRow =
                fn TC.OutputType (FType.RowExt (_, {field = (label', fieldt), ext})) =>
                    if label' = label
                    then fieldt
                    else coerceRow ext
        in coerce typ
        end
end

