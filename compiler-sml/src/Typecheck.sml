structure Typecheck :> sig
    exception Unbound of Pos.t * Name.t

    val typecheck: Cst.stmt vector -> Cst.stmt vector
end = struct
    exception Unbound of Pos.t * Name.t

    val rootEnv = NameSortedMap.empty

    val constType = fn Const.Int _ => Type.Prim Type.Int

    fun typecheck program =
        let fun check (ctx as (env, level)) =
                fn Cst.Use (pos, name) =>
                    let val t = case NameSortedMap.find (env, name)
                                of SOME t => Type.instantiate level t
                                 | NONE => raise Unbound (pos, name)
                    in (Cst.Use (pos, name), t)
                    end
                 | Cst.Const (pos, c) => (Cst.Const (pos, c), constType c)

            and checkStmt (ctx as (env, level)) =
                fn Cst.Def (pos, name, expr) =>
                    let val (expr', t) = check ctx expr
                        val goalT = NameSortedMap.lookup (env, name) (* can't raise *)
                    in Type.unify goalT t
                     ; (Cst.Def (pos, name, expr'), t)
                    end

            fun checkStmts (ctx as (env, level)) stmts =
                let (* The level of the rhs expressions: *)
                    val level' = Type.pushLevel level
                    (* Add unbound type variables for each definee: *)
                    val env' = Vector.foldl (fn (Cst.Def (_, name, _), env) =>
                                                 let val t = Type.fresh level'
                                                 in NameSortedMap.insert (env, name, t)
                                                 end)
                                            env stmts
                    (* Check each stmt in env' and level': *)
                in Vector.map (#1 o checkStmt (env', level')) stmts
                end
        in checkStmts (rootEnv, Type.topLevel) program
        end
end
