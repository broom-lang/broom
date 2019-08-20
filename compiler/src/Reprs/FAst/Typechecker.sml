structure FAstTypechecker :> sig
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
        val insertCo: t * Name.t * FFType.concr * FFType.concr -> t
        val findCo: t * Name.t -> (FFType.concr * FFType.concr) option
    end = struct
        type t = { vals: FFType.concr NameSortedMap.map
                 , types: (Id.t * FFType.kind) Id.SortedMap.map
                 , coercions: (FFType.concr * FFType.concr) NameSortedMap.map }

        val empty =
            {vals = NameSortedMap.empty, types = Id.SortedMap.empty, coercions = NameSortedMap.empty}

        fun insert ({vals, types, coercions}, name, t) =
            {vals = NameSortedMap.insert (vals, name, t), types, coercions}
        fun insertType ({vals, types, coercions}, id, entry) =
            {vals, types = Id.SortedMap.insert (types, id, entry), coercions}
        fun insertCo ({vals, types, coercions}, name, l, r) =
            {vals, types, coercions = NameSortedMap.insert (coercions, name, (l, r))}

        fun find ({vals, ...}: t, name) = NameSortedMap.find (vals, name)
        fun findType ({types, ...}: t, id) = Id.SortedMap.find (types, id)
        fun findCo ({coercions, ...}: t, name) = NameSortedMap.find (coercions, name)
    end

    datatype kind = datatype FAst.Type.kind
    datatype concr = datatype FAst.Type.concr'
    datatype abs = datatype FAst.Type.abs'
    datatype co = datatype FAst.Type.co'
    datatype expr = datatype FAst.Term.expr
    datatype stmt = datatype FAst.Term.stmt

    fun pushStmts env stmts =
        let fun pushStmt (stmt, env) =
                case stmt
                of Val (_, {var, typ}, _) => Env.insert (env, var, typ)
                 | Axiom (_, name, l, r) => Env.insertCo (env, name, l, r)
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
                 | _ => NONE
        in rewrite row
        end

    fun rowLabelType row label =
        case row
        of RowExt (_, {field = (label', fieldt), ext}) =>
            if label' = label
            then SOME fieldt
            else rowLabelType ext label
         | EmptyRow _ => NONE
         | _ => raise Fail ("Not a row type: " ^ FType.Concr.toString row)

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
            in eq env (body, body')
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
         | (CallTFn (_, callee, args), CallTFn (_, callee', args')) =>
            callee = callee'
            andalso Vector.all (eq env) (Vector.zip (args, args'))
         | (UseT (_, {var, ...}), UseT (_, {var = var', ...})) =>
            (case Env.findType (env, var)
             of SOME (id, _) => (case Env.findType (env, var')
                                 of SOME (id', _) => id = id'
                                  | NONE => raise Fail ("Out of scope: g__" ^ Id.toString var'))
              | NONE => raise Fail ("Out of scope: g__" ^ Id.toString var))
         | (Prim (_, p), Prim (_, p')) => p = p' (* HACK? *)
         | _ => raise Fail (FFType.Concr.toString t ^ " /= " ^ FFType.Concr.toString t')
    
    and absEq env =
        fn (Exists (_, params, body), Exists (_, params', body')) => 
            let val env = Vector.foldl (fn ({var, kind}, env) => Env.insertType (env, var, (var, kind)))
                                       env params
                val env = Vector.foldl (fn ({var, kind}, env) => Env.insertType (env, var, (var, kind)))
                                       env params'
            in eq env (body, body')
            end

    fun checkEq env ts = if eq env ts
                         then ()
                         else raise Fail (FFType.concrToString (#1 ts) ^ " != " ^ FFType.concrToString (#2 ts))

    fun checkCo env =
        fn Refl t => (t, t)
         | Symm co => Pair.flip (checkCo env co)
         | UseCo name => (case Env.findCo (env, name)
                          of SOME co => co
                           | NONE => raise Fail ("Unbound coercion " ^ Name.toString name))

    fun check env =
        fn Fn f => checkFn env f
         | TFn f => checkTFn env f
         | Extend ext => checkExtend env ext
         | Override ovr => checkOverride env ovr
         | App app => checkApp env app
         | TApp app => checkTApp env app
         | Field access => checkField env access
         | Let lett => checkLet env lett
         (*| If iff => checkIf env iff*)
         | Match match => raise Fail "unimplemented"
         | Cast cast => checkCast env cast
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
            fun checkRowField ((label, field), row) =
                RowExt (pos, {field = (label, check env field), ext = row})
            val t = Record (pos, Vector.foldr checkRowField recordRow fields)
        in checkEq env (typ, t)
         ; typ
        end

    and checkOverride env (pos, typ, fields, original) =
        let val recordRow = case check env original
                            of Record (_, row) => row
                             | t => raise Fail ("Not a record: " ^ FFTerm.exprToString original ^ ": " ^ FFType.Concr.toString t)
            fun override ((label, field), row) =
                case row
                of RowExt (pos, {field = (label', fieldt), ext}) =>
                    if label = label'
                    then RowExt (pos, {field = (label, check env field), ext})
                    else RowExt (pos, {field = (label', fieldt), ext = override ((label, field), ext)})
                 | _ => raise Fail ("Tried to override missing field " ^ Name.toString label)
            val t = Record (pos, Vector.foldr override recordRow fields)
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
                
                fun checkArg ({var = _, kind}, arg) = checkKindEq (FFType.Concr.kindOf arg, kind)
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
             of SOME fieldt => 
                 ( checkEq env (fieldt, typ)
                 ; fieldt )
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

    and checkCast env (_, typ, expr, co) =
        let val exprT = check env expr
            val (fromT, toT) = checkCo env co
        in checkEq env (exprT, fromT)
         ; checkEq env (toT, typ)
         ; typ
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
         | Axiom _ => () (* TODO: Some checks here (see F_c paper) *)
         | Expr expr => ignore (check env expr)

    fun typecheckProgram {typeFns, axioms, body} =
        let val env = Vector.foldl (fn ((name, l, r), env) => Env.insertCo (env, name, l, r))
                                   Env.empty axioms
        in check env body (* TODO: Use `typeFns`, `axioms` *)
         ; NONE
        end
end

