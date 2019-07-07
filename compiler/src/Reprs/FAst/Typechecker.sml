structure FAstTypechecker :> sig
    val typecheck: FixedFAst.Term.expr -> ((* FIXME: *) unit, FixedFAst.Type.concr) Either.t
    val typecheckProgram: FixedFAst.Term.program -> (* FIXME: *) unit option
end = struct
    structure FAst = FixedFAst
    structure FType = FAst.Type
    structure Id = FType.Id
    structure FFType = FAst.Type
    structure Prim = FFType.Prim
    structure FFTerm = FAst.Term

    structure Env :> sig
        type t

        val empty: t
        val insert: t * Name.t * FFType.concr -> t
        val insertType: t * Id.t * (Id.t * FFType.kind) -> t
        val find: t * Name.t -> FFType.concr option
        val findType: t * Id.t -> (Id.t * FFType.kind) option
    end = struct
        type t = { vals: FFType.concr NameSortedMap.map
                 , types: (Id.t * FFType.kind) Id.SortedMap.map }

        val empty = {vals = NameSortedMap.empty, types = Id.SortedMap.empty}
        fun insert ({vals, types}, name, t) = {vals = NameSortedMap.insert (vals, name, t), types}
        fun insertType ({vals, types}, id, entry) = {vals, types = Id.SortedMap.insert (types, id, entry)}
        fun find ({vals, ...}: t, name) = NameSortedMap.find (vals, name)
        fun findType ({types, ...}: t, id) = Id.SortedMap.find (types, id)
    end

    datatype kind = datatype FAst.Type.kind
    datatype concr = datatype FAst.Type.concr'
    datatype abs = datatype FAst.Type.abs'
    datatype expr = datatype FAst.Term.expr
    datatype stmt = datatype FAst.Term.stmt

    fun pushStmts env stmts =
        let fun pushStmt (stmt, env) =
                case stmt
                of Val (_, {var, typ}, _) => Env.insert (env, var, typ)
                 | Expr _ => env
        in Vector.foldl pushStmt env stmts
        end

    fun rewriteRow label row =
        let val rec rewrite = 
                fn (RowExt (pos, row as {field = (flabel, ftype), ext})) =>
                    if flabel = label
                    then SOME row
                    else Option.map (fn {field, ext} =>
                                         {field, ext = RowExt (pos, {field = (flabel, ftype), ext})})
                                    (rewrite ext)
                 | t => NONE
        in rewrite row
        end

    fun rowLabelType row label =
        case row
        of RowExt (_, {field = (label', fieldt), ext}) =>
            if label' = label
            then SOME fieldt
            else rowLabelType ext label
         | EmptyRow _ => NONE

    val rec kindEq =
        fn (ArrowK _, ArrowK _) => raise Fail "unimplemented"
         | (TypeK _, TypeK _) => true
         | (RowK _, RowK _) => true
         | _ => false

    fun checkKindEq kinds = if kindEq kinds
                            then ()
                            else raise Fail (FFType.kindToString (#1 kinds) ^ " != " ^ FFType.kindToString (#2 kinds))

    fun eq env (t, t') =
        case (t, t')
        of (ForAll (_, params, body), ForAll (_, params', body')) =>
            let val env = Vector.foldl (fn ({var, kind}, env) => Env.insertType (env, var, (var, kind)))
                                       env params
                val env = Vector.foldl (fn ({var, kind}, env) => Env.insertType (env, var, (var, kind)))
                                       env params'
            in eq env (body, body)
            end
         | (Arrow (_, {domain, codomain}), Arrow (_, {domain = domain', codomain = codomain'})) =>
            eq env (domain, domain') andalso eq env (codomain, codomain')
         | (Record (_, row), Record (_, row')) => eq env (row, row')
         | (RowExt (_, {field = (label, fieldt), ext}), row' as RowExt _) =>
            (case rewriteRow label row'
             of SOME {field = (_, fieldt'), ext = ext'} =>
                 eq env (fieldt, fieldt') andalso eq env (ext, ext')
              | NONE => false)
         | (EmptyRow _, EmptyRow _) => true
         | (FType.Type (_, t), FType.Type (_, t')) => absEq env (t, t')
         | (UseT (_, {var, ...}), UseT (_, {var = var', ...})) =>
            (case Env.findType (env, var)
             of SOME (id, _) => (case Env.findType (env, var')
                                 of SOME (id', _) => id = id'
                                  | NONE => raise Fail ("Out of scope: g__" ^ Id.toString var'))
              | NONE => raise Fail ("Out of scope: g__" ^ Id.toString var))
         | (Prim (_, p), Prim (_, p')) => p = p' (* HACK? *)
    
    and absEq env =
        fn (Exists (_, #[], t), Exists (_, #[], t')) => eq env (t, t')
         | (Exists (pos, params, body), Exists (pos', params', body')) => 
            if Vector.length params = Vector.length params'
            then raise Fail "unimplemented"
            else false

    fun checkEq env ts = if eq env ts
                         then ()
                         else raise Fail (FFType.concrToString (#1 ts) ^ " != " ^ FFType.concrToString (#2 ts))

    fun check env =
        fn Fn f => checkFn env f
         | TFn f => checkTFn env f
         | Extend ext => checkExtend env ext
         | App app => checkApp env app
         | TApp app => checkTApp env app
         | Field access => checkField env access
         | Let lett => checkLet env lett
         | If iff => checkIf env iff
         | Use use => checkUse env use
         | Type (pos, t) => FFType.Type (pos, t)
         | Const (pos, c) => Prim (pos, Const.typeOf c)

    and checkFn env (pos, {var = param, typ = domain}, body) =
        let val env = Env.insert (env, param, domain)
        in Arrow (pos, {domain, codomain = check env body})
        end

    and checkTFn env (pos, params, body) =
        let val env = Vector.foldl (fn ({var, kind}, env) => Env.insertType (env, var, (var, kind)))
                                   env params
        in ForAll (pos, params, check env body)
        end

    and checkExtend env (pos, typ, fields, orec) =
        let val recordRow = case orec
                            of SOME record =>
                                (case check env record
                                 of Record (_, row) => row
                                  | t => raise Fail ("Not a record: " ^ FFTerm.exprToString record ^ ": " ^ FFType.concrToString t))
                             | NONE => EmptyRow pos
            fun checkRowField ((label, fieldt), row) =
                RowExt (pos, {field = (label, check env fieldt), ext = row})
            val t = Record (pos, Vector.foldr checkRowField recordRow fields)
        in checkEq env (typ, t)
         ; typ
        end

    and checkApp env (_, typ, {callee, arg}) =
        case check env callee
        of Arrow (_, {domain, codomain}) =>
            let val argType = check env arg
            in checkEq env (argType, domain)
             ; checkEq env (codomain, typ)
             ; typ
            end
         | t => raise Fail ("Uncallable: " ^ FFTerm.exprToString callee ^ ": " ^ FFType.concrToString t)

    and checkTApp env (_, typ, {callee, args}) =
        case check env callee
        of ForAll (_, params, body) =>
            let do if Vector.length args = Vector.length params then () else raise Fail "argument count"
                val pargs = Vector.zip (params, args)
                
                fun checkArg ({var, kind}, arg) = checkKindEq (FFType.Concr.kindOf arg, kind)
                do Vector.app checkArg pargs

                val mapping = Vector.foldl (fn (({var, ...}, arg), mapping) =>
                                                Id.SortedMap.insert (mapping, var, arg))
                                           Id.SortedMap.empty pargs
                val typ' = FFType.Concr.substitute (Fn.constantly false) mapping body
            in checkEq env (typ', typ)
             ; typ
            end
         | t => raise Fail ("Nonuniversal: " ^ FFTerm.exprToString callee ^ ": " ^ FFType.concrToString t)

    and checkField env (_, typ, expr, label) =
        case check env expr
        of t as Record (_, row) =>
            (case rowLabelType row label
             of SOME fieldt => fieldt
              | NONE => raise Fail ("Record " ^ FFTerm.exprToString expr ^ ": " ^ FFType.concrToString t
                                    ^ " does not have field " ^ Name.toString label))
         | t => raise Fail ("Not a record: " ^ FFTerm.exprToString expr ^ ": " ^ FFType.concrToString t)

    and checkLet env (_, stmts, body) =
        let val env = pushStmts env stmts
        in Vector.app (checkStmt env) stmts
         ; check env body
        end

    and checkIf env (pos, cond, conseq, alt) =
        let do checkEq env (check env cond, Prim (pos, Prim.Bool))
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

    fun typecheckProgram {typeFns, axioms, body} =
        ( check Env.empty body (* TODO: Use `typeFns`, `axioms` *)
        ; NONE )
end

