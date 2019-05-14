structure FAstTypechecker :> sig
    val typecheck: FixedFAst.Term.expr -> ((* FIXME: *) unit, FixedFAst.Type.typ) Either.t
end = struct
    structure FFType = FixedFAst.Type
    type typ = FFType.typ
    structure FFTerm = FixedFAst.Term

    structure Env :> sig
        type t

        val empty: t
        val insert: t * Name.t * typ -> t
        val find: t * Name.t -> typ option
    end = struct
        type t = typ NameSortedMap.map

        val empty = NameSortedMap.empty
        val insert = NameSortedMap.insert
        val find = NameSortedMap.find
    end

    datatype typ = datatype FAst.Type.typ
    datatype ftyp = datatype FFType.typ
    datatype expr = datatype FAst.Term.expr
    datatype stmt = datatype FAst.Term.stmt

    fun pushStmts env stmts =
        let fun pushStmt (stmt, env) =
                case stmt
                of Val (_, {var, typ}, _) => Env.insert (env, var, typ)
                 | Expr _ => env
        in Vector.foldl pushStmt env stmts
        end

    fun eq env (Fix t, Fix t') =
        case (t, t')
        of (Arrow (_, {domain, codomain}), Arrow (_, {domain = domain', codomain = codomain'})) =>
            eq env (domain, domain') andalso eq env (codomain, codomain')
         | (EmptyRow _, EmptyRow _) => true
         | (FFType.Type (_, t), FFType.Type (_, t')) => eq env (t, t')
         | (Prim (_, p), Prim (_, p')) => p = p' (* HACK? *)

    fun checkEq env ts = if eq env ts
                         then ()
                         else raise Fail (FFType.toString (#1 ts) ^ " != " ^ FFType.toString (#2 ts))

    fun check env =
        fn App app => checkApp env app
         | Let lett => checkLet env lett
         | Use use => checkUse env use
         | Type (pos, t) => Fix (FFType.Type (pos, t))
         | Const (pos, c) => Fix (Prim (pos, Const.typeOf c))

    and checkApp env (_, typ, {callee, arg}) =
        case check env callee
        of Fix (Arrow (_, {domain, codomain})) =>
            let val argType = check env arg
            in checkEq env (argType, domain)
             ; checkEq env (codomain, typ)
             ; typ
            end
         | t => raise Fail ("Uncallable: " ^ FFTerm.toString callee ^ ": " ^ FFType.toString t)

    and checkLet env (_, stmts, body) =
        let val env = pushStmts env stmts
        in Vector.app (checkStmt env) stmts
         ; check env body
        end

    and checkUse env (pos, {var, typ}) =
        let val t = case Env.find (env, var)
                    of SOME t => t
                     | NONE => raise Fail ("Out of scope: " ^ Name.toString var ^ " at " ^ Pos.toString pos)
        in checkEq env (typ, t)
         ; typ
        end

    and checkStmt env =
        fn Val (_, {typ, ...}, expr) =>
            let val exprType = check env expr
            in checkEq env (exprType, typ)
            end
         | Expr expr => ignore (check env expr)

    val typecheck = Either.Right o check Env.empty
end
