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

    datatype value
        = Uninitialized
        | Initialized
        | Closure of Support.set

    structure Ctx :> sig
        type t

        val empty : t
        val pushStmts : t -> stmt vector -> t
        val initialize : t -> Name.t -> value -> t

        val find : t -> Name.t -> value
    end = struct
        structure Bindings = NameSortedMap

        type t = value Bindings.map

        val empty = Bindings.empty

        fun pushStmts ctx stmts =
            Vector.foldl (fn (Axiom _, ctx) => ctx
                           | (Val (_, {var, typ = _}, _), ctx) =>
                              Bindings.insert (ctx, var, Uninitialized))
                         ctx stmts

        fun initialize ctx name value = Bindings.insert (ctx, name, value)

        (* `Bindings.lookup` is appropriate since unbound variables are already caught: *)
        fun find ctx name = Bindings.lookup (ctx, name)
    end

    fun checkExpr ctx : expr -> value * Support.set =
        fn Let args => checkLet ctx args
         | Use args => checkUse ctx args

    and checkLet ctx (_, stmts, body) =
        let val (ctx, stmtsSupport) = checkStmts ctx stmts
            val (value, bodySupport) = checkExpr ctx body
        in (value, Support.union (stmtsSupport, bodySupport))
        end

    and checkUse ctx (pos, {var, typ = _}) =
        case Ctx.find ctx var
        of Uninitialized => 
            raise Fail ("Uninitialized " ^ Name.toString var ^ " in " ^ Pos.toString pos ^ "\n")
         | v as Initialized | v as Closure _ => (v, Support.empty)

    and checkStmt ctx : stmt -> Ctx.t * Support.set =
        fn Axiom _ => (ctx, Support.empty)
         | Val (_, {var, typ = _}, expr) =>
            let val (value, support) = checkExpr ctx expr
            in (Ctx.initialize ctx var value, support)
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

