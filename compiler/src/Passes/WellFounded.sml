structure WellFounded :> sig
    structure FAst : sig
        structure Term : FAST_TERM
            where type stmt = FixedFAst.Term.stmt
            where type Type.sv = FixedFAst.Type.sv
    end

    datatype error = ReadUninitialized of Pos.t * Name.t

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
        type ord_key = t

        val compare : t * t -> order
    end = struct
        type t = ScopeId.t * Name.t
        type ord_key = t

        fun compare ((scopeId, name), (scopeId', name')) =
            case ScopeId.compare (scopeId, scopeId')
            of EQUAL => Name.compare (name, name')
             | ord => ord
    end

    datatype error = ReadUninitialized of Pos.t * Name.t

    structure Support = BinarySetFn(ScopedId)

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

    fun rewriteRow label row =
        let val rec rewrite = 
                fn (RowExt (row as {field = (flabel, ftype), ext})) =>
                    if flabel = label
                    then SOME row
                    else Option.map (fn {field, ext} =>
                                         {field, ext = RowExt {field = (flabel, ftype), ext}})
                                    (rewrite ext)
                 | _ => NONE
        in rewrite row
        end

    val rec join : typ * typ -> typ * bool =
        fn (ForAll (params, body), ForAll (params', body')) =>
            let val (typ, changed) = join (body, body')
            in (ForAll (params', typ), changed)
            end
         | (Closure (support, codomain), Closure (support', codomain')) =>
            let val (codomain, codomainChanged) = join (codomain, codomain')
            in ( Closure (Support.union (support, support'), codomain)
               , codomainChanged orelse not (Support.equal (support, support')) )
            end
         | (Record row, Record row') =>
            let val (row, changed) = join (row, row')
            in (Record row, changed)
            end
         | (RowExt {field = (label, fieldt), ext}, row' as RowExt _) =>
            (case rewriteRow label row'
             of SOME {field = (_, fieldt'), ext = ext'} =>
                 let val (fieldt, fieldtChanged) = join (fieldt, fieldt')
                     val (ext, extChanged) = join (ext, ext')
                 in ( RowExt {field = (label, fieldt), ext}
                    , fieldtChanged orelse extChanged )
                 end
              | NONE => raise Fail "unreachable")
         | (EmptyRow, EmptyRow) => (EmptyRow, false)
         | (typ as UseT _, UseT _) => (typ, false)
         | (typ as Scalar, Scalar) => (typ, false)
         | _ => raise Fail "unreachable"

    structure Env :> sig
        type t

        structure Builder : sig
            type builder
            type bindings = typ NameHashTable.hash_table

            val new : ScopeId.t -> builder
            val pushScope : builder -> {parent : ScopeId.t, scope : ScopeId.t}
                          -> unit
            val insert : builder -> ScopedId.t -> typ -> unit
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

            fun new topScopeId =
                let val builder = ScopeId.HashTable.mkTable (0, Subscript)
                    val chain = [NameHashTable.mkTable (0, Subscript)]
                    do ScopeId.HashTable.insert builder (topScopeId, chain)
                in builder
                end

            fun pushScope builder {parent, scope = scopeId} =
                let val chain = NameHashTable.mkTable (0, Subscript) 
                              :: ScopeId.HashTable.lookup builder parent
                in ScopeId.HashTable.insert builder (scopeId, chain)
                end

            fun insert builder (scopeId, name) typ =
                ScopeId.HashTable.lookup builder scopeId
                |> List.hd
                |> (fn bs => NameHashTable.insert bs (name, typ))

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

    fun initialProgramEnv {axioms = _, typeFns = _, scope = topScopeId, stmts} =
        let val builder = Env.Builder.new topScopeId

            fun insertExpr scopeId =
                fn Let (_, scopeId', stmts, body) =>
                    ( Env.Builder.pushScope builder {parent = scopeId, scope = scopeId'}
                    ; Vector.app (insertStmt scopeId') stmts
                    ; insertExpr scopeId' body )
                 | Match (_, _, matchee, clauses) =>
                    ( insertExpr scopeId matchee
                    ; Vector.app (fn {pattern, body} =>
                                      let val scopeId = insertPat scopeId pattern
                                      in insertExpr scopeId body
                                      end)
                                 clauses )
                 | Fn (_, scopeId', {var, typ}, _, body) =>
                    ( Env.Builder.pushScope builder {parent = scopeId, scope = scopeId'}
                    ; Env.Builder.insert builder (scopeId', var) (elaborateType typ)
                    ; insertExpr scopeId' body )
                 | TFn (_, _, _, body) => insertExpr scopeId body
                 | App (_, _, {callee, arg}) =>
                    ( insertExpr scopeId callee
                    ; insertExpr scopeId arg )
                 | TApp (_, _, {callee, args = _}) => insertExpr scopeId callee
                 | Extend (_, _, fields, ext) =>
                    ( Vector.app (fn (_, expr) => insertExpr scopeId expr) fields
                    ; Option.app (insertExpr scopeId) ext )
                 | Override (_, _, fields, ext) =>
                    ( Vector.app (fn (_, expr) => insertExpr scopeId expr) fields
                    ; insertExpr scopeId ext )
                 | Field (_, _, expr, _) => insertExpr scopeId expr
                 | Cast (_, _, expr, _) => insertExpr scopeId expr
                 | Type _ | Use _ | Const _ => ()
            
            and insertStmt scopeId =
                fn Axiom _ => ()
                 | Val (_, {var, typ}, expr) =>
                    ( Env.Builder.insert builder (scopeId, var) (elaborateType typ)
                    ; insertExpr scopeId expr )
                 | Expr expr => insertExpr scopeId expr

            and insertPat scopeId =
                fn AnnP (_, {pat, typ = _}) => insertPat scopeId pat
                 | Def (_, scopeId', {var, typ}) =>
                    ( Env.Builder.pushScope builder {parent = scopeId, scope = scopeId'}
                    ; Env.Builder.insert builder (scopeId', var) (elaborateType typ)
                    ; scopeId' )
                 | ConstP _ => scopeId
        in Vector.app (insertStmt topScopeId) stmts
         ; Env.Builder.build builder
        end

    datatype context = Escaping | Naming

    datatype state = Uninitialized | Initialized

    datatype access
        = Instant of state
        | Delayed of state

    structure IniEnv :> sig
        type t

        val empty : t
        val pushBlock : t -> Name.t list -> t
        val initialize : t -> Name.t -> unit
        val pushMatch : t -> Name.t -> t
        val pushFn : t -> context -> Name.t -> t

        val access : t -> Name.t -> access
    end = struct
        datatype frame
            = BlockFrame of state NameHashTable.hash_table
            | MatchFrame of Name.t
            | FnFrame of context * Name.t

        type t = frame list

        val empty = []

        fun pushBlock ini names =
            let val bindings = NameHashTable.mkTable (0, Subscript)
                do List.app (fn name => NameHashTable.insert bindings (name, Uninitialized))
                            names
            in BlockFrame bindings :: ini
            end

        fun initialize ini name =
            let val rec init =
                    fn BlockFrame bs :: frames =>
                        if NameHashTable.inDomain bs name
                        then NameHashTable.insert bs (name, Initialized)
                        else init frames
                     | FnFrame _ :: frames => init frames
                     | [] => raise Fail "unreachable"
            in init ini
            end

        fun pushMatch ini name = MatchFrame name :: ini

        fun pushFn ini ctx name = FnFrame (ctx, name) :: ini

        fun access ini name =
            let fun inited stateToAccess =
                    fn BlockFrame bs :: frames =>
                        (case NameHashTable.find bs name
                         of SOME state => stateToAccess state
                          | NONE => inited stateToAccess frames)
                     | MatchFrame name' :: frames =>
                        if name = name'
                        then stateToAccess Initialized
                        else inited stateToAccess frames
                     | FnFrame (ctx, name') :: frames =>
                        if name = name'
                        then stateToAccess Initialized
                        else let val stateToAccess = case ctx
                                                     of Escaping => stateToAccess
                                                      | Naming => Delayed
                             in inited stateToAccess frames
                             end
                     | [] => raise Fail "unreachable"
            in inited Instant ini
            end
    end

    fun checkProgram (program as {axioms = _, typeFns = _, scope = topScopeId, stmts}) =
        let val env = initialProgramEnv program
            val changed = ref false
            
            fun checkExpr scopeId ini ctx =
                fn Fn (_, scopeId, {var, ...}, _, body) =>
                    let val ini = IniEnv.pushFn ini ctx var
                        val (codomain, support) = checkExpr scopeId ini ctx body
                    in case ctx
                       of Escaping => (Closure (Support.empty, codomain), support)
                        | Naming => (Closure (support, codomain), Support.empty)
                    end
                 | Let (_, scopeId, stmts, body) =>
                    let val ini = pushBlock ini stmts
                        val stmtsSupport = checkStmts scopeId ini stmts
                        val (typ, bodySupport) = checkExpr scopeId ini ctx body
                    in (typ, Support.union (stmtsSupport, bodySupport))
                    end
                 | Match (_, _, matchee, clauses) =>
                    let val (_, matcheeSupport) = checkExpr scopeId ini ctx matchee
                        val (SOME clausesTyp, clausesSupport) =
                            Vector.foldl (fn (clause, (_, support)) =>
                                              let val (clauseTyp, clauseSupport) =
                                                      checkClause scopeId ini ctx clause
                                              in ( SOME clauseTyp
                                                 , Support.union (support, clauseSupport) )
                                              end)
                                         (NONE, Support.empty) clauses
                    in (clausesTyp, Support.union (matcheeSupport, clausesSupport))
                    end
                 | App (_, _, {callee, arg}) =>
                    (case checkExpr scopeId ini Escaping callee
                     of (Closure (_, codomain), calleeSupport) =>
                         (*       ^-- should be empty because context was `Escaping`. *)
                         let val (_, argSupport) = checkExpr scopeId ini Escaping arg
                         in (codomain, Support.union (calleeSupport, argSupport))
                         end
                      | _ => raise Fail "unreachable")
                 | Use (pos, {var, ...}) =>
                    (case IniEnv.access ini var
                     of Delayed Initialized | Instant Initialized => (* ok unsupported *)
                         (Env.lookup env (scopeId, var), Support.empty)
                      | Delayed Uninitialized => (* ok with support *)
                         (Env.lookup env (scopeId, var), Support.singleton (scopeId, var))
                      | Instant Uninitialized => (* error *)
                         raise Fail ( "uninitialized " ^ Name.toString var
                                    ^ " in " ^ Pos.toString pos ))
                 | Cast (_, _, expr, _) => checkExpr scopeId ini ctx expr
                 | Type _ | Const _ => (Scalar, Support.empty)

            and pushBlock ini stmts =
                let val names =
                        Vector.foldl (fn (Axiom _, names) => names
                                       | (Val (_, {var, ...}, _), names) => var :: names
                                       | (Expr _, names) => names)
                                     [] stmts
                in IniEnv.pushBlock ini names
                end

            and checkStmts scopeId ini stmts =
                Vector.foldl (fn (stmt, support) =>
                                  Support.union (support, checkStmt scopeId ini stmt))
                             Support.empty stmts

            and checkStmt scopeId ini =
                fn Axiom _ => Support.empty
                 | Val (_, {var, typ = _}, expr) =>
                    let val (typ, support) = checkExpr scopeId ini Naming expr
                        val refineChanged = Env.refine env (scopeId, var) typ
                        do changed := (!changed orelse refineChanged)
                        do IniEnv.initialize ini var
                    in support
                    end
                 | Expr expr => #2 (checkExpr scopeId ini Escaping expr)

            and checkClause scopeId ini ctx {pattern, body} =
                let val (scopeId, ini) = checkPattern scopeId ini ctx pattern
                in checkExpr scopeId ini ctx body
                end

            and checkPattern scopeId ini ctx =
                fn Def (_, scopeId, {var, ...}) => (scopeId, IniEnv.pushMatch ini var)
                 | ConstP _ => (scopeId, ini)
        in checkStmts topScopeId (pushBlock IniEnv.empty stmts) stmts
         ; Either.Right ()
        end
end

