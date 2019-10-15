structure WellFounded :> sig
    structure FAst : sig
        structure Term : FAST_TERM
            where type stmt = FixedFAst.Term.stmt
            where type Type.sv = FixedFAst.Type.sv
    end

    datatype error = Uninitialized of Pos.t * Name.t

    val checkProgram : FAst.Term.program -> (error, unit) Either.t
end = struct
    structure FAst = FixedFAst
    structure FTerm = FAst.Term
    structure FType = FAst.Type
    datatype expr = datatype FTerm.expr
    datatype stmt = datatype FTerm.stmt
    datatype pat = datatype FTerm.pat
    val op|> = Fn.|>

    structure ScopedId :> sig
        type t = ScopeId.t * Name.t
    end = struct
        type t = ScopeId.t * Name.t
    end

    datatype error = Uninitialized of Pos.t * Name.t

    (* FIXME: Should be a set of ScopedId.t *)
    structure Support = NameSortedSet

    datatype typ
        = ForAll of FType.def vector * typ
        | Closure of Support.set * typ
        | Record of typ
        | RowExt of {field : Name.t * typ, ext : typ}
        | EmptyRow
        | UseT of FType.def
        | Scalar

    val rec elaborateType : FType.concr -> typ =
        fn FType.ForAll (_, params, body) => ForAll (params, elaborateType body)
         | FType.Arrow (_, _, {domain = _, codomain}) =>
            Closure (Support.empty, elaborateType codomain)
         | FType.Record (_, row) => Record (elaborateType row)
         | FType.RowExt (_, {field = (label, fieldt), ext}) =>
            RowExt { field = (label, elaborateType fieldt)
                   , ext = elaborateType ext }
         | FType.EmptyRow _ => EmptyRow
         | FType.Type _ => Scalar
         | FType.App _ => Scalar
         | FType.CallTFn _ => Scalar
         | FType.UseT (_, def) => UseT def
         | FType.SVar _ => raise Fail "unreachable"
         | FType.Prim _ => Scalar

    val rec join : typ * typ -> typ * bool =
        fn _ => raise Fail "unimplemented"

    structure Env :> sig
        type t

        structure Builder : sig
            type builder
            type bindings = typ NameHashTable.hash_table

            val new : unit -> builder
            val pushScope : builder
                          -> {parent : ScopeId.t, scope : ScopeId.t * bindings}
                          -> unit
            val build : builder -> t
        end

        (* Join the `typ` at the `ScopedId.t` with the `typ`
           and return whether the `typ` was changed by the join: *)
        val refine : t -> ScopedId.t -> typ -> bool
        val lookup : t -> ScopedId.t -> typ
    end = struct
        type bindings = typ NameHashTable.hash_table

        type t = bindings list ScopeId.HashTable.hash_table

        structure Builder = struct
            type builder = t
            type bindings = bindings

            fun new () = ScopeId.HashTable.mkTable (0, Subscript)

            fun pushScope builder {parent, scope = (scopeId, bindings)} =
                let val chain = bindings :: ScopeId.HashTable.lookup builder parent
                in ScopeId.HashTable.insert builder (scopeId, chain)
                end

            val build = Fn.identity
        end

        fun lookup env (scopeId, name) =
            let val rec get =
                    fn scope :: scopes =>
                        (case NameHashTable.find scope name
                         of SOME typ => typ
                          | NONE => get scopes)
                     | [] => raise Fail "unreachable"
            in get (ScopeId.HashTable.lookup env scopeId)
            end

        fun update env (scopeId, name) f =
            let val rec modify =
                    fn scope :: scopes =>
                        (case NameHashTable.find scope name
                         of SOME typ => NameHashTable.insert scope (name, f typ)
                          | NONE => modify scopes)
                     | [] => raise Fail "unreachable"
            in modify (ScopeId.HashTable.lookup env scopeId)
            end

        fun refine env scopedName typ' =
            let val changed = ref false
            in update env scopedName (fn typ =>
                   let val (joined, change) = join (typ, typ')
                       do changed := change
                   in joined
                   end
               )
             ; !changed
            end
    end

    fun checkProgram {axioms = _, typeFns = _, stmts} =
        raise Fail "unimplemented"

    (*
    datatype typ
        = Uninitialized
        | Initialized
        | Closure of typ * Support.set
        | ForAll of FType.def vector * typ * Support.set
        | Record of typ
        | RowExt of {field: Name.t * typ, ext: typ}
        | EmptyRow
        | Scalar

    structure Ctx :> sig
        type t

        val empty : t
        val pushStmts : t -> stmt vector -> t
        val initialize : t -> Name.t -> typ -> t
        val pushParam : t -> Name.t -> typ -> t

        val find : t -> Name.t -> typ
    end = struct
        structure Bindings = NameSortedMap

        type t = typ Bindings.map

        val empty = Bindings.empty

        fun pushStmts ctx stmts =
            Vector.foldl (fn (Val (_, {var, typ = _}, _), ctx) =>
                              Bindings.insert (ctx, var, Uninitialized)
                           | (Axiom _, ctx) | (Expr _, ctx) => ctx)
                         ctx stmts

        fun initialize ctx name typ = Bindings.insert (ctx, name, typ)

        val pushParam = initialize

        (* `Bindings.lookup` is appropriate since unbound variables are already caught: *)
        fun find ctx name = Bindings.lookup (ctx, name)
    end

    fun substitute mapping =
        fn t as Scalar => t

    fun elaborateType ctx =
        fn FType.Arrow (_, _, {domain = _, codomain}) =>
            (* TODO: Quantification over support of box domain. *)
            (* FIXME: `Support.empty`?! *)
            Closure (elaborateType ctx codomain, Support.empty)
         | FType.Record (_, row) => Record (elaborateType ctx row)
         | FType.RowExt (_, {field = (label, fieldt), ext}) =>
            RowExt { field = (label, elaborateType ctx fieldt)
                   , ext = elaborateType ctx ext }
         | FType.EmptyRow _ => EmptyRow
         | FType.Type _ | FType.Prim _ | FType.UseT _ => Scalar
         | t => raise Fail ("unimplemented: " ^ PPrint.pretty 80 (FType.Concr.toDoc t))

    fun checkExpr ctx : expr -> typ * Support.set =
        fn Let args => checkLet ctx args
         | Fn args => checkFn ctx args
         | TFn args => checkTFn ctx args
         | App args => checkApp ctx args
         | TApp args => checkTApp ctx args
         | Match args => checkMatch ctx args
         | Extend args => checkExtend ctx args
         | Override args => checkOverride ctx args
         | Field args => checkField ctx args
         | Cast args => checkCast ctx args
         | Use args => checkUse ctx args
         | Type _ | Const _ => (Scalar, Support.empty)
         | e => raise Fail ("unimplemented: " ^ PPrint.pretty 80 (FTerm.exprToDoc e))

    and checkLet ctx (_, scopeId, stmts, body) =
        let val (ctx, stmtsSupport) = checkStmts ctx stmts
            val (typ, bodySupport) = checkExpr ctx body
        in (typ, Support.union (stmtsSupport, bodySupport))
        end

    and checkFn ctx (_, scopeId, {var = param, typ = paramTyp}, _, body) =
        let val ctx = Ctx.pushParam ctx param (elaborateType ctx paramTyp)
        in (Closure (checkExpr ctx body), Support.empty)
        end

    and checkTFn ctx (_, scopeId, params, body) =
        let val (codomain, bodySupport) = checkExpr ctx body
        in (ForAll (params, codomain, bodySupport), Support.empty)
        end

    and checkApp ctx (_, _, {callee, arg}) =
        case checkExpr ctx callee
        of (Closure (codomain, bodySupport), calleeSupport) =>
            let val (_, argSupport) = checkExpr ctx arg
            in (codomain, Support.union (bodySupport, Support.union (calleeSupport, argSupport)))
            end
         | _ => raise Fail "unreachable"

    and checkTApp ctx (_, _, {callee, args}) =
        case checkExpr ctx callee
        of (ForAll (params, codomain, bodySupport), calleeSupport) =>
            let val mapping =
                    (params, args)
                    |> Vector.zipWith (fn ({var, ...}, arg) => (var, arg))
                    |> FType.Id.SortedMap.fromVector
            in ( substitute mapping codomain
               , Support.union (calleeSupport, bodySupport) )
            end
         | _ => raise Fail "unreachable"

    and checkMatch ctx (_, _, matchee, clauses) =
        let val (_, matcheeSupport) = checkExpr ctx matchee
            val (typ, clausesSupport) = checkClauses ctx clauses
        in (typ, Support.union (matcheeSupport, clausesSupport))
        end

    and checkClauses ctx clauses =
        let fun step (clause, (_, support)) =
                let val (typ, clauseSupport) = checkClause ctx clause
                in (SOME typ, Support.union (support, clauseSupport))
                end
        in case Vector.foldl step (NONE, Support.empty) clauses
           of (SOME typ, support) => (typ, support)
        end

    and checkClause ctx {pattern, body} =
        let val ctx = checkPat ctx pattern
        in checkExpr ctx body
        end

    and checkPat ctx =
        fn Def (_, scopeId, {var, typ}) => Ctx.pushParam ctx var (elaborateType ctx typ)
         | ConstP _ => ctx
         | pat => raise Fail ("unimplemented: " ^ PPrint.pretty 80 (FTerm.patternToDoc pat))

    and checkExtend ctx (_, t, fields, ext) =
        let val fieldsSupport =
                Vector.foldl (fn ((label, fielde), support) =>
                                  let val (_, fieldSupport) = checkExpr ctx fielde
                                  in Support.union (support, fieldSupport)
                                  end)
                             Support.empty fields
            val extSupport =
                case ext
                of SOME ext => #2 (checkExpr ctx ext)
                 | NONE => Support.empty
        in (elaborateType ctx t, Support.union (fieldsSupport, extSupport))
        end

    and checkOverride ctx (_, t, fields, ext) =
        let val fieldsSupport =
                Vector.foldl (fn ((label, fielde), support) =>
                                  let val (_, fieldSupport) = checkExpr ctx fielde
                                  in Support.union (support, fieldSupport)
                                  end)
                             Support.empty fields
            val extSupport = #2 (checkExpr ctx ext)
        in (elaborateType ctx t, Support.union (fieldsSupport, extSupport))
        end

    and checkField ctx (_, t, expr, label) =
        let val (_, support) = checkExpr ctx expr
        in (elaborateType ctx t, support)
        end

    and checkCast ctx (_, t, expr, _) =
        let val (_, support) = checkExpr ctx expr
        in (elaborateType ctx t, support)
        end

    and checkUse ctx (pos, {var, typ = _}) =
        case Ctx.find ctx var
        of Uninitialized => 
            raise Fail ("Uninitialized " ^ Name.toString var ^ " in " ^ Pos.toString pos ^ "\n")
         | t => (t, Support.empty)

    and checkStmt ctx : stmt -> Ctx.t * Support.set =
        fn Axiom _ => (ctx, Support.empty)
         | Val (_, {var, typ = _}, expr) =>
            let val (typ, support) = checkExpr ctx expr
            in (Ctx.initialize ctx var typ, support)
            end
         | Expr expr =>
            let val (_, support) = checkExpr ctx expr
            in (ctx, support)
            end

    (* TODO: Check that stmts have no escaping effects when env has uninitialized variables
             that are not outside the nearest fn contour. (First ensure that this is the right
             restriction to prevent double initializations in all cases.) *)
    and checkStmts ctx stmts =
        let val ctx = Ctx.pushStmts ctx stmts
        in Vector.foldl (fn (stmt, (ctx, supportAcc)) =>
                             let val (ctx, stmtSupport) = checkStmt ctx stmt
                             in (ctx, Support.union (supportAcc, stmtSupport))
                             end)
                        (ctx, Support.empty) stmts
        end

    fun checkProgram {axioms = _, typeFns = _, stmts} =
        let val (_, support) = checkStmts Ctx.empty stmts
        in Support.isEmpty support
        end *)
end

