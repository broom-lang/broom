structure FAstTypechecker :> sig
    val typecheck: FixedFAst.Term.expr -> ((* FIXME: *) unit, FixedFAst.Type.typ) Either.t
end = struct
    structure FFType = FixedFAst.Type
    structure Prim = FFType.Prim
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

    fun rowLabelType (Fix row) label =
        case row
        of RowExt (_, {field = (label', fieldt), ext}) =>
            if label' = label
            then SOME fieldt
            else rowLabelType ext label
         | EmptyRow _ => NONE

    fun eq env (ft as Fix t, ft' as Fix t') =
        case (t, t')
        of (ForAll _, _) | (_, ForAll _) => raise Fail "unimplemented"
         | (Arrow (_, {domain, codomain}), Arrow (_, {domain = domain', codomain = codomain'})) =>
            eq env (domain, domain') andalso eq env (codomain, codomain')
         | (Record (_, row), Record (_, row')) => eq env (row, row')
         | (RowExt (_, {field = (label, fieldt), ext}), RowExt (_, {field = (label', fieldt'), ext = ext'})) =>
            label = label' andalso eq env (fieldt, fieldt') andalso eq env (ext, ext')
         | (EmptyRow _, EmptyRow _) => true
         | (FFType.Type (_, t), FFType.Type (_, t')) => eq env (t, t')
         | (UseT _, _) | (_, UseT _) => raise Fail "unimplemented"
         | (Prim (_, p), Prim (_, p')) => p = p' (* HACK? *)

    fun checkEq env ts = if eq env ts
                         then ()
                         else raise Fail (FFType.toString (#1 ts) ^ " != " ^ FFType.toString (#2 ts))

    fun check env =
        fn Fn f => checkFn env f
         | Extend ext => checkExtend env ext
         | App app => checkApp env app
         | Field access => checkField env access
         | Let lett => checkLet env lett
         | If iff => checkIf env iff
         | Use use => checkUse env use
         | Type (pos, t) => Fix (FFType.Type (pos, t))
         | Const (pos, c) => Fix (Prim (pos, Const.typeOf c))

    and checkFn env (pos, {var = param, typ = domain}, body) =
        let val env = Env.insert (env, param, domain)
        in Fix (Arrow (pos, {domain, codomain = check env body}))
        end

    and checkExtend env (pos, typ, fields, orec) =
        let val recordRow = case orec
                            of SOME record =>
                                (case check env record
                                 of Fix (Record (_, row)) => row
                                  | t => raise Fail ("Not a record: " ^ FFTerm.toString record ^ ": " ^ FFType.toString t))
                             | NONE => Fix (EmptyRow pos)
            fun checkRowField ((label, fieldt), row) =
                Fix (RowExt (pos, {field = (label, check env fieldt), ext = row}))
            val t = Fix (Record (pos, Vector.foldr checkRowField recordRow fields))
        in checkEq env (typ, t)
         ; typ
        end

    and checkApp env (_, typ, {callee, arg}) =
        case check env callee
        of Fix (Arrow (_, {domain, codomain})) =>
            let val argType = check env arg
            in checkEq env (argType, domain)
             ; checkEq env (codomain, typ)
             ; typ
            end
         | t => raise Fail ("Uncallable: " ^ FFTerm.toString callee ^ ": " ^ FFType.toString t)

    and checkField env (_, typ, expr, label) =
        case check env expr
        of t as Fix (Record (_, row)) =>
            (case rowLabelType row label
             of SOME fieldt => fieldt
              | NONE => raise Fail ("Record " ^ FFTerm.toString expr ^ ": " ^ FFType.toString t
                                    ^ " does not have field " ^ Name.toString label))
         | t => raise Fail ("Not a record: " ^ FFTerm.toString expr ^ ": " ^ FFType.toString t)

    and checkLet env (_, stmts, body) =
        let val env = pushStmts env stmts
        in Vector.app (checkStmt env) stmts
         ; check env body
        end

    and checkIf env (pos, cond, conseq, alt) =
        let do checkEq env (check env cond, Fix (Prim (pos, Prim.Bool)))
            val ct = check env conseq
            do checkEq env (ct, check env alt)
        in ct
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

