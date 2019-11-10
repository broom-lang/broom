structure FAstTypechecker :> sig
    val typecheckProgram: FixedFAst.Term.program -> (* FIXME: *) unit option
end = struct
    structure FAst = FixedFAst
    structure FType = FAst.Type
    structure Id = FType.Id
    structure FFType = FAst.Type
    structure Concr = FFType.Concr
    structure FFTerm = FAst.Term
    val op|> = Fn.|>

    structure Env :> sig
        type t

        val empty: Pos.sourcemap -> t
        val insert: t * Name.t * FFType.concr -> t
        val insertType: t * Id.t * (Id.t * FFType.kind) -> t
        val insertTypeFn: t * Name.t * FFType.tfn_sig -> t

        val find: t * Name.t -> FFType.concr option
        val findType: t * Id.t -> (Id.t * FFType.kind) option
        val findTypeFn: t * Name.t -> FFType.tfn_sig option
        val insertCo: t * Name.t * FFType.concr * FFType.concr -> t
        val findCo: t * Name.t -> (FFType.concr * FFType.concr) option

        val sourcemap : t -> Pos.sourcemap
    end = struct
        type t = { vals: FFType.concr NameSortedMap.map
                 , types: (Id.t * FFType.kind) Id.SortedMap.map
                 , typeFns: FFType.tfn_sig NameSortedMap.map
                 , coercions: (FFType.concr * FFType.concr) NameSortedMap.map
                 , sourcemap: Pos.sourcemap }

        fun empty sourcemap =
            { vals = NameSortedMap.empty, types = Id.SortedMap.empty
            , typeFns = NameSortedMap.empty, coercions = NameSortedMap.empty
            , sourcemap }

        fun insert ({vals, types, typeFns, coercions, sourcemap}, name, t) =
            {vals = NameSortedMap.insert (vals, name, t), types, typeFns, coercions, sourcemap}
        fun insertType ({vals, types, typeFns, coercions, sourcemap}, id, entry) =
            {vals, types = Id.SortedMap.insert (types, id, entry), typeFns, coercions, sourcemap}
        fun insertTypeFn ({vals, types, typeFns, coercions, sourcemap}, name, tfkind) =
            {vals, types, typeFns = NameSortedMap.insert (typeFns, name, tfkind), coercions, sourcemap}
        fun insertCo ({vals, types, typeFns, coercions, sourcemap}, name, l, r) =
            {vals, types, typeFns, coercions = NameSortedMap.insert (coercions, name, (l, r)), sourcemap}

        fun find ({vals, ...}: t, name) = NameSortedMap.find (vals, name)
        fun findType ({types, ...}: t, id) = Id.SortedMap.find (types, id)
        fun findTypeFn ({typeFns, ...}: t, id) = NameSortedMap.find (typeFns, id)
        fun findCo ({coercions, ...}: t, name) = NameSortedMap.find (coercions, name)

        val sourcemap: t -> Pos.sourcemap = #sourcemap
    end

    datatype kind = datatype FAst.Type.kind
    datatype concr = datatype FAst.Type.concr'
    datatype co = datatype FAst.Type.co'
    datatype expr = datatype FAst.Term.expr
    datatype stmt = datatype FAst.Term.stmt
    datatype pat = datatype FAst.Term.pat

    val rewriteRow = FAst.Type.Concr.rewriteRow

    fun pushStmts env stmts =
        let fun pushStmt (stmt, env) =
                case stmt
                of Val (_, {var, typ, ...}, _) => Env.insert (env, var, typ)
                 | Axiom (_, name, l, r) => Env.insertCo (env, name, l, r)
                 | Expr _ => env
        in Vector1.foldl pushStmt env stmts
        end

    fun rowLabelType row label =
        case row
        of RowExt {base, field = (label', fieldt)} =>
            if label' = label
            then SOME fieldt
            else rowLabelType base label
         | EmptyRow => NONE
         | _ => raise Fail ("Not a row type: " ^ FType.Concr.toString row)

    fun rowWhere row (field' as (label', _)) =
        case row
        of RowExt {base, field = field as (label, _)} =>
            if label = label'
            then RowExt {base, field = field'}
            else RowExt {base = rowWhere base field', field}
         | _ => raise Fail ("Tried to override missing field " ^ Name.toString label')

    fun kindOf env =
        let fun findTypeFnExn name =
                case Env.findTypeFn (env, name)
                of SOME tfkind => tfkind
                 | NONE => raise Fail ("Unbound type function " ^ Name.toString name)
        in FFType.Concr.kindOf findTypeFnExn
        end

    val rec kindEq =
        fn (ArrowK _, ArrowK _) => raise Fail "unimplemented"
         | (TypeK, TypeK) => true
         | (RowK, RowK) => true
         | (CallsiteK, CallsiteK) => true
         | _ => false

    fun checkKindEq kinds = if kindEq kinds
                            then ()
                            else raise Fail (FFType.kindToString (#1 kinds) ^ " != " ^ FFType.kindToString (#2 kinds))

    fun skolemize env ((params, body), (params', body')) f =
        let do Vector1.zip (params, params') (* FIXME: arity errors *)
               |> Vector1.app (fn ({kind, var = _}, {kind = kind', var = _}) =>
                                   if kind = kind'
                                   then ()
                                   else raise Fail "inequal kinds")
            val params'' = Vector1.map (fn {kind, var = _} => {var = Id.fresh (), kind}) params
            val env = Vector1.foldl (fn ({var, kind}, env) => Env.insertType (env, var, (var, kind)))
                                    env params''
            val mapping = (params, params'')
                        |> Vector1.zipWith (fn ({var, ...}, def') => (var, UseT def'))
                        |> Vector1.toVector
                        |> Id.SortedMap.fromVector
            val body = Concr.substitute Fn.undefined mapping body
            val mapping' = (params', params'')
                         |> Vector1.zipWith (fn ({var, ...}, def') => (var, UseT def'))
                         |> Vector1.toVector
                         |> Id.SortedMap.fromVector
            val body' = Concr.substitute Fn.undefined mapping' body'
        in f env (body, body')
        end

    fun eq env (t, t') =
        case (t, t')
        of (Exists existential, Exists existential') => 
            skolemize env (existential, existential') eq
         | (ForAll universal, ForAll universal') =>
            skolemize env (universal, universal') eq
         | (Arrow (expl, {domain, codomain}), Arrow (expl', {domain = domain', codomain = codomain'})) =>
            expl = expl'
            andalso eq env (domain, domain')
            andalso eq env (codomain, codomain')
         | (Record row, Record row') => eq env (row, row')
         | (RowExt {base, field = (label, fieldt)}, row' as RowExt _) =>
            (case rewriteRow label row'
             of SOME {base = base', field = (_, fieldt')} =>
                 eq env (fieldt, fieldt') andalso eq env (base, base')
              | NONE => false)
         | (EmptyRow, EmptyRow) => true
         | (FType.Type t, FType.Type t') => eq env (t, t')
         | (FType.App {callee, args}, FType.App {callee = callee', args = args'}) =>
            eq env (callee, callee')
            andalso Vector1.all (eq env) (Vector1.zip (args, args'))
         | (CallTFn (callee, args), CallTFn (callee', args')) =>
            callee = callee'
            andalso Vector.all (eq env) (Vector.zip (args, args'))
         | (UseT {var, ...}, UseT {var = var', ...}) =>
            (case Env.findType (env, var)
             of SOME (id, _) => (case Env.findType (env, var')
                                 of SOME (id', _) => id = id'
                                  | NONE => raise Fail ("Out of scope: g__" ^ Id.toString var'))
              | NONE => raise Fail ("Out of scope: g__" ^ Id.toString var))
         | (Prim p, Prim p') => p = p' (* HACK? *)
         | _ => false

    fun checkEq currPos env ts =
        if eq env ts
        then ()
        else raise Fail ( FFType.concrToString (#1 ts) ^ " != " ^ FFType.concrToString (#2 ts)
                        ^ " in " ^ Pos.spanToString (Env.sourcemap env) currPos )

    fun checkCo env =
        fn Refl t => (t, t)
         | Symm co => Pair.flip (checkCo env co)
         | InstCo {callee, args} =>
            (case checkCo env callee
             of (ForAll (defs, l), ForAll (defs', r)) =>
                 ( Vector1.zip3With (fn ({kind, ...}, {kind = kind', ...}, arg) =>
                                         ( checkKindEq (kind, kind')
                                         ; checkKindEq (kindOf env arg, kind) ))
                                    (defs, defs', args)
                 ; let val mapping = (defs, args)
                                   |> Vector1.zipWith (Pair.first #var)
                                   |> Vector1.toVector
                                   |> Id.SortedMap.fromVector
                       val mapping' = (defs', args)
                                    |> Vector1.zipWith (Pair.first #var)
                                    |> Vector1.toVector
                                    |> Id.SortedMap.fromVector
                   in ( FType.Concr.substitute (Fn.constantly false) mapping l
                      , FType.Concr.substitute (Fn.constantly false) mapping' r )
                   end ))
         | UseCo name => (case Env.findCo (env, name)
                          of SOME co => co
                           | NONE => raise Fail ("Unbound coercion " ^ Name.toString name))

    fun check env =
        fn Fn f => checkFn env f
         | TFn f => checkTFn env f
         | EmptyRecord _ => FFType.Record FFType.EmptyRow
         | With args => checkWith env args
         | Where args => checkWhere env args
         | App app => checkApp env app
         | TApp app => checkTApp env app
         | Field access => checkField env access
         | Let lett => checkLet env lett
         | Match match => checkMatch env match
         | Cast cast => checkCast env cast
         | Use use => checkUse env use
         | Type (_, t) => FFType.Type t
         | Const (_, c) => Prim (Const.typeOf c)

    and checkFn env (pos, {pos = _, id = _, var = param, typ = domain}, expl, body) =
        let val env = Env.insert (env, param, domain)
        in Arrow (expl, {domain, codomain = check env body})
        end

    and checkTFn env (pos, params, body) =
        let val env = Vector1.foldl (fn ({var, kind}, env) => Env.insertType (env, var, (var, kind)))
                                    env params
        in ForAll (params, check env body)
        end

    and checkWith env (pos, typ, {base, field = (label, fieldExpr)}) =
        let val Record baseRow = check env base
            val t = Record (RowExt {base = baseRow, field = (label, check env fieldExpr)})
        in checkEq pos env (typ, t)
         ; typ
        end

    and checkWhere env (pos, typ, {base, field = (label, fieldExpr)}) =
        let val Record baseRow = check env base
            val t = Record (rowWhere baseRow (label, check env fieldExpr))
        in checkEq pos env (typ, t)
         ; typ
        end

    and checkApp env (pos, typ, {callee, arg}) =
        case check env callee
        of Arrow (_, {domain, codomain}) =>
            let val argType = check env arg
            in checkEq pos env (argType, domain)
             ; checkEq pos env (codomain, typ)
             ; typ
            end
         | t => raise Fail ("Uncallable: " ^ FFTerm.exprToString callee ^ ": " ^ FFType.concrToString t)

    and checkTApp env (pos, typ, {callee, args}) =
        case check env callee
        of ForAll (params, body) =>
            let do if Vector1.length args = Vector1.length params then () else raise Fail "argument count"
                val pargs = Vector1.zip (params, args)
                
                fun checkArg ({var = _, kind}, arg) = checkKindEq (kindOf env arg, kind)
                do Vector1.app checkArg pargs

                val mapping = Vector1.foldl (fn (({var, ...}, arg), mapping) =>
                                                 Id.SortedMap.insert (mapping, var, arg))
                                            Id.SortedMap.empty pargs
                val typ' = FFType.Concr.substitute (Fn.constantly false) mapping body
            in checkEq pos env (typ', typ)
             ; typ
            end
         | t => raise Fail ("Nonuniversal: " ^ FFTerm.exprToString callee ^ ": " ^ FFType.concrToString t)

    and checkField env (pos, typ, expr, label) =
        case check env expr
        of t as Record row =>
            (case rowLabelType row label
             of SOME fieldt => 
                 ( checkEq pos env (fieldt, typ)
                 ; fieldt )
              | NONE => raise Fail ("Record " ^ FFTerm.exprToString expr ^ ": " ^ FFType.concrToString t
                                    ^ " does not have field " ^ Name.toString label))
         | t => raise Fail ("Not a record: " ^ FFTerm.exprToString expr ^ ": " ^ FFType.concrToString t)

    and checkLet env (_, stmts, body) =
        let val env = pushStmts env stmts
        in Vector1.app (checkStmt env) stmts
         ; check env body
        end

    and checkMatch env (pos, typ, matchee, clauses) =
        let val matcheeTyp = check env matchee
            val clauseTypes = Vector.map (checkClause env matcheeTyp) clauses
        in Vector.app (fn clauseTyp => checkEq pos env (clauseTyp, typ)) clauseTypes
         ; typ
        end

    and checkClause env matcheeTyp {pattern, body} =
        let val env = checkPattern env matcheeTyp pattern
        in check env body
        end

    and checkPattern env matcheeTyp =
        fn Def (_, {pos = _, id, var, typ}) => Env.insert (env, var, typ)
         | ConstP (pos, c) => (checkEq pos env (Prim (Const.typeOf c), matcheeTyp); env)

    and checkCast env (pos, typ, expr, co) =
        let val exprT = check env expr
            val (fromT, toT) = checkCo env co
        in checkEq pos env (exprT, fromT)
         ; checkEq pos env (toT, typ)
         ; typ
        end

    and checkUse env (pos, {pos = _, id = _, var, typ}) =
        let val t = case Env.find (env, var)
                    of SOME t => t
                     | NONE => raise Fail ( "Out of scope: " ^ Name.toString var ^ " at "
                                          ^ Pos.spanToString (Env.sourcemap env) pos )
        in checkEq pos env (typ, t)
         ; typ
        end

    and checkStmt env =
        fn Val (pos, {typ, ...}, expr) =>
            let val exprType = check env expr
            in checkEq pos env (exprType, typ)
            end
         | Axiom _ => () (* TODO: Some checks here (see F_c paper) *)
         | Expr expr => ignore (check env expr)

    fun typecheckProgram {typeFns, stmts, sourcemap} =
        let val env = Vector.foldl (fn ((name, kindSig), env) => Env.insertTypeFn (env, name, kindSig))
                                   (Env.empty sourcemap) typeFns
            val env =
                case Vector1.fromVector stmts
                of SOME stmts => pushStmts env stmts
                 | NONE => env
        in Vector.app (checkStmt env) stmts (* TODO: Use `typeFns` *)
         ; NONE
        end
end

