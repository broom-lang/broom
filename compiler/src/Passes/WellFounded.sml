structure WellFounded :> sig
    structure FAst : sig
        structure Term : FAST_TERM
            where type stmt = FixedFAst.Term.stmt
            where type Type.sv = FixedFAst.Type.sv
    end

    val checkProgram: FAst.Term.program -> bool
end = struct
    structure FAst = FixedFAst
    structure FTerm = FAst.Term
    datatype expr = datatype FTerm.expr
    datatype stmt = datatype FTerm.stmt

    structure Support = NameSortedSet

    datatype typ
        = Uninitialized
        | Initialized
        | Closure of typ * Support.set
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
            Vector.foldl (fn (Axiom _, ctx) => ctx
                           | (Val (_, {var, typ = _}, _), ctx) =>
                              Bindings.insert (ctx, var, Uninitialized))
                         ctx stmts

        fun initialize ctx name typ = Bindings.insert (ctx, name, typ)

        val pushParam = initialize

        (* `Bindings.lookup` is appropriate since unbound variables are already caught: *)
        fun find ctx name = Bindings.lookup (ctx, name)
    end

    fun elaborateType ctx =
        fn FType.Prim _ => Scalar

    fun checkExpr ctx : expr -> typ * Support.set =
        fn Let args => checkLet ctx args
         | Fn args => checkFn ctx args
         | App args => checkApp ctx args
         | Use args => checkUse ctx args

    and checkLet ctx (_, stmts, body) =
        let val (ctx, stmtsSupport) = checkStmts ctx stmts
            val (typ, bodySupport) = checkExpr ctx body
        in (typ, Support.union (stmtsSupport, bodySupport))
        end

    and checkFn ctx (_, {var = param, typ = paramTyp}, _, body) =
        let val ctx = Ctx.pushParam ctx param (elaborateType ctx paramTyp)
        in (Closure (checkExpr ctx body), Support.empty)
        end

    and checkApp ctx (_, _, {callee, arg}) =
        case checkExpr ctx callee
        of (Closure (codomain, bodySupport), calleeSupport) =>
            let val (_, argSupport) = checkExpr ctx arg
            in (codomain, Support.union (bodySupport, Support.union (calleeSupport, argSupport)))
            end
         | _ => raise Fail "unreachable"

    and checkUse ctx (pos, {var, typ = _}) =
        case Ctx.find ctx var
        of Uninitialized => 
            raise Fail ("Uninitialized " ^ Name.toString var ^ " in " ^ Pos.toString pos ^ "\n")
         | v as Initialized | v as Closure _ => (v, Support.empty)

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
        end
end

