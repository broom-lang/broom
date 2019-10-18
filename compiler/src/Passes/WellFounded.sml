structure WellFounded :> sig
    structure FAst : sig
        structure Term : FAST_TERM
            where type stmt = FixedFAst.Term.stmt
            where type Type.sv = FixedFAst.Type.sv
    end

    datatype error = ReadUninitialized of Pos.t * Name.t option * Name.t
    
    val errorToDoc : error -> PPrint.t

    val checkProgram : FAst.Term.program -> (error vector, unit) Either.t
end = struct
    structure FAst = FixedFAst
    structure FTerm = FAst.Term
    structure FType = FAst.Type
    datatype expr = datatype FTerm.expr
    datatype stmt = datatype FTerm.stmt
    datatype pat = datatype FTerm.pat
    val op|> = Fn.|>
    val space = PPrint.space
    val text = PPrint.text
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>

    datatype error = ReadUninitialized of Pos.t * Name.t option * Name.t

    fun errorToDoc (ReadUninitialized (pos, via, name)) =
        text "Error: Cannot prove that" <+> Name.toDoc name
            <+> (case via
                 of SOME via => PPrint.parens (text "via" <+> Name.toDoc via) <> PPrint.space
                  | NONE => PPrint.empty)
            <> text "is initialized in" <+> text (Pos.toString pos)

    structure Def :> sig
        type t = FTerm.def
        type ord_key = t

        val toDoc : t -> PPrint.t
        val compare : t * t -> order
    end = struct
        type t = FTerm.def
        type ord_key = t

        val toDoc = FTerm.defToDoc

        fun compare ({id, ...}: t, {id = id', ...}: t) =
            DefId.compare (id, id')
    end

    structure Support = struct
        structure Super = BinarySetFn(Def)
        open Super

        fun toDoc names =
            names
            |> toList
            |> Vector.fromList
            |> Vector.map Def.toDoc
            |> PPrint.punctuate (text "," <> space)
            |> PPrint.braces
    end

    datatype typ
        = Closure of Support.set * typ
        | Record of typ
        | RowExt of {field : Name.t * typ, ext : typ}
        | EmptyRow
        | Scalar
        | Unknown

    val rec typToDoc =
        fn Closure (support, codomain) =>
            text "_" <+> text "->" <+> Support.toDoc support
                <+> typToDoc codomain
         | Record row => PPrint.braces (typToDoc row)
         | row as RowExt _ | row as EmptyRow => rowToDoc row
         | Scalar => text "scalar"
         | Unknown => text "?"

    and rowToDoc =
        fn RowExt {field = (label, fieldt), ext} =>
            let val fieldDoc = Name.toDoc label <+> text ":" <+> typToDoc fieldt
            in case ext
               of EmptyRow => fieldDoc
                | _ => fieldDoc <> text "," <+> rowToDoc ext
            end
         | EmptyRow => PPrint.empty
         | row => typToDoc row

    val rec elaborateType : FType.concr -> typ =
        fn FType.ForAll (_, body) => elaborateType body
         | FType.Arrow (_, {domain = _, codomain}) =>
            Closure (Support.empty, elaborateType codomain)
         | FType.Record row => Record (elaborateType row)
         | FType.RowExt {field = (label, fieldt), ext} =>
            RowExt { field = (label, elaborateType fieldt)
                   , ext = elaborateType ext }
         | FType.EmptyRow => EmptyRow
         | FType.Type _ => Scalar
         | FType.App _ => Scalar
         | FType.CallTFn _ => Scalar
         | FType.UseT _ => Scalar
         | FType.SVar _ => raise Fail "unreachable"
         | FType.Prim _ => Scalar

    fun rewriteRow label row =
        let val rec rewrite = 
                fn RowExt (row as {field = (flabel, ftype), ext}) =>
                    if flabel = label
                    then SOME row
                    else Option.map (fn {field, ext} =>
                                         {field, ext = RowExt {field = (flabel, ftype), ext}})
                                    (rewrite ext)
                 | _ => NONE
        in rewrite row
        end

    fun withField row field = RowExt {field, ext = row}

    fun whereField row (field as (label, _)) =
        Option.map (fn {field = _, ext} => withField ext field)
                   (rewriteRow label row)

    fun rowField row label =
        let val rec get =
                fn RowExt {field = (label', fieldt), ext} =>
                    if label = label'
                    then SOME fieldt
                    else get ext
                 | _ => NONE
        in get row
        end

    val rec accessTyp : typ -> typ * Support.set =
        fn Closure (support, codomain) =>
            let val (codomain, codomainSupport) = accessTyp codomain
            in ( Closure (Support.empty, codomain)
               , Support.union (support, codomainSupport) )
            end
         | Record row => Pair.first Record (accessTyp row)
         | RowExt {field = (label, fieldt), ext} =>
            let val (fieldt, fieldSupport) = accessTyp fieldt
                val (ext, extSupport) = accessTyp ext
            in ( RowExt {field = (label, fieldt), ext}
               , Support.union (fieldSupport, extSupport) )
            end
         | typ as EmptyRow | typ as Scalar | typ as Unknown =>
            (typ, Support.empty)

    val rec join : typ * typ -> typ * bool =
        fn (Closure (support, codomain), Closure (support', codomain')) =>
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
         | (typ as Scalar, Scalar) => (typ, false)
         | (Unknown, Unknown) => (Unknown, false)
         | (Unknown, typ) => (typ, true)
         | (typ, Unknown) => (typ, false)
         | (typ, typ') =>
            raise Fail (PPrint.pretty 80 ( text "unreachable:"
                                           <+> typToDoc typ <+> text "V" <+> typToDoc typ' ))

    structure Env :> sig
        type t

        structure Builder : sig
            type builder

            val new : ScopeId.t -> builder
            val insert : builder -> DefId.t -> typ -> unit
            val build : builder -> t
        end

        (* Join the `typ` at the `ScopedId.t` with the `typ`
           and return whether the `typ` was changed by the join: *)
        val refine : t -> DefId.t -> typ -> bool
        val lookup : t -> DefId.t -> typ
    end = struct
        type t = typ DefId.HashTable.hash_table

        structure Builder = struct
            type builder = t

            fun new topScopeId = DefId.HashTable.mkTable (0, Subscript)

            fun insert builder id typ = DefId.HashTable.insert builder (id, typ)

            val build = Fn.identity
        end

        val lookup = DefId.HashTable.lookup

        fun update env id f =
            let val typ = DefId.HashTable.lookup env id
            in DefId.HashTable.insert env (id, f typ)
            end

        fun refine env id typ' =
            let val changed = ref false
            in update env id (fn typ =>
                   let val (joined, change) = join (typ, typ')
                       do changed := change
                   in joined
                   end
               )
             ; !changed
            end
    end

    (* TODO: Just initialize everything to `Unknown`. *)
    fun initialProgramEnv {axioms = _, typeFns = _, scope = topScopeId, stmts} =
        let val builder = Env.Builder.new topScopeId

            fun insertExpr scopeId =
                fn Let (_, scopeId', stmts, body) =>
                    ( Vector.app (insertStmt scopeId') stmts
                    ; insertExpr scopeId' body )
                 | Match (_, _, matchee, clauses) =>
                    ( insertExpr scopeId matchee
                    ; Vector.app (fn {pattern, body} =>
                                      let val scopeId = insertPat scopeId pattern
                                      in insertExpr scopeId body
                                      end)
                                 clauses )
                 | Fn (_, scopeId', {id, typ, ...}, _, body) =>
                    ( Env.Builder.insert builder id (elaborateType typ)
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
                 | Val (_, {id, typ, ...}, expr) =>
                    ( Env.Builder.insert builder id (elaborateType typ)
                    ; insertExpr scopeId expr )
                 | Expr expr => insertExpr scopeId expr

            and insertPat scopeId =
                fn AnnP (_, {pat, typ = _}) => insertPat scopeId pat
                 | Def (_, scopeId', {id, typ, ...}) =>
                    ( Env.Builder.insert builder id (elaborateType typ)
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
        val pushBlock : t -> DefId.t list -> t
        val initialize : t -> DefId.t -> unit
        val pushMatch : t -> DefId.t -> t
        val pushFn : t -> context -> DefId.t -> t

        val access : t -> DefId.t -> access
    end = struct
        datatype frame
            = BlockFrame of state DefId.HashTable.hash_table
            | MatchFrame of DefId.t
            | FnFrame of context * DefId.t

        type t = frame list

        val empty = []

        fun pushBlock ini names =
            let val bindings = DefId.HashTable.mkTable (0, Subscript)
                do List.app (fn name => DefId.HashTable.insert bindings (name, Uninitialized))
                            names
            in BlockFrame bindings :: ini
            end

        fun initialize ini name =
            let val rec init =
                    fn BlockFrame bs :: frames =>
                        if DefId.HashTable.inDomain bs name
                        then DefId.HashTable.insert bs (name, Initialized)
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
                        (case DefId.HashTable.find bs name
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
            val errors = ref []
            fun error err = errors := err :: !errors
            
            fun checkExpr scopeId ini ctx =
                fn Fn (_, scopeId, {id, ...}, _, body) =>
                    let val ini = IniEnv.pushFn ini ctx id
                        val (codomain, support) = checkExpr scopeId ini ctx body
                    in case ctx
                       of Escaping => (Closure (Support.empty, codomain), support)
                        | Naming => (Closure (support, codomain), Support.empty)
                    end
                 | TFn (_, _, _, body) => checkExpr scopeId ini ctx body
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
                      | (_, calleeSupport) =>
                         let val (_, argSupport) = checkExpr scopeId ini Escaping arg
                         in (Unknown, Support.union (calleeSupport, argSupport))
                         end)
                 | TApp (_, _, {callee, args = _}) => checkExpr scopeId ini ctx callee
                 | Extend (_, _, fields, ext) =>
                    let val (Record ext, extSupport) =
                            case ext
                            of SOME ext => checkExpr scopeId ini ctx ext
                             | NONE => (Record EmptyRow, Support.empty)
                        val (row, support) =
                            Vector.foldl (fn ((label, expr), (typ, support)) =>
                                              let val (fieldt, fieldSupport) = checkExpr scopeId ini ctx expr
                                              in ( withField typ (label, fieldt)
                                                 , Support.union (support, fieldSupport) )
                                              end)
                                         (ext, extSupport) fields
                    in (Record row, support)
                    end
                 | Override (_, _, fields, ext) =>
                    let val (Record ext, extSupport) = checkExpr scopeId ini ctx ext
                        val (row, support) =
                            Vector.foldl (fn ((label, expr), (typ, support)) =>
                                              let val (fieldt, fieldSupport) = checkExpr scopeId ini ctx expr
                                              in ( valOf (whereField typ (label, fieldt))
                                                 , Support.union (support, fieldSupport) )
                                              end)
                                         (ext, extSupport) fields
                    in (Record row, support)
                    end
                 | Field (_, _, expr, label) =>
                    let val (recTyp, support) = checkExpr scopeId ini ctx expr
                    in ( case recTyp
                         of RowExt _ => valOf (rowField recTyp label)
                          | _ => Unknown
                       , support )
                    end
                 | Use (pos, def as {id, var, ...}) =>
                    let fun access ini via (def as {id, var, ...}) =
                            case IniEnv.access ini (#id def)
                            of Delayed Initialized | Instant Initialized => (* ok unsupported: *)
                                Support.empty
                             | Delayed Uninitialized => (* ok with support: *)
                                Support.singleton def
                             | Instant Uninitialized => (* error: *)
                                ( error (ReadUninitialized (pos, via, #var def))
                                ; Support.empty ) (* support won't help, so claim not to need any *)

                        val immediateSupport = access ini NONE def
                        val (typ, transitiveSupport) =
                            case ctx
                            of Escaping => (* access transitively: *)
                                let val (typ, typSupport) = accessTyp (Env.lookup env id)
                                    val support =
                                        Support.foldl (fn (def, support) =>
                                                           Support.union ( support
                                                                         , access ini (SOME var) def ))
                                                      Support.empty typSupport
                                in (typ, support)
                                end
                             | Naming => (* delayed propagation of support though type: *)
                                (Env.lookup env id, Support.empty)
                    in (typ, Support.union (immediateSupport, transitiveSupport))
                    end
                 | Cast (_, _, expr, _) => checkExpr scopeId ini ctx expr
                 | Type _ | Const _ => (Scalar, Support.empty)

            and pushBlock ini stmts =
                let val ids =
                        Vector.foldl (fn (Axiom _, ids) => ids
                                       | (Val (_, {id, ...}, _), ids) => id :: ids
                                       | (Expr _, ids) => ids)
                                     [] stmts
                in IniEnv.pushBlock ini ids
                end

            and checkStmts scopeId ini stmts =
                Vector.foldl (fn (stmt, support) =>
                                  Support.union (support, checkStmt scopeId ini stmt))
                             Support.empty stmts

            and checkStmt scopeId ini =
                fn Axiom _ => Support.empty
                 | Val (_, {id, typ = _, ...}, expr) =>
                    let val (typ, support) = checkExpr scopeId ini Naming expr
                        val refineChanged = Env.refine env id typ
                        do changed := (!changed orelse refineChanged)
                        do IniEnv.initialize ini id
                    in support
                    end
                 | Expr expr => #2 (checkExpr scopeId ini Escaping expr)

            and checkClause scopeId ini ctx {pattern, body} =
                let val (scopeId, ini) = checkPattern scopeId ini ctx pattern
                in checkExpr scopeId ini ctx body
                end

            and checkPattern scopeId ini ctx =
                fn Def (_, scopeId, {id, ...}) => (scopeId, IniEnv.pushMatch ini id)
                 | ConstP _ => (scopeId, ini)

            fun iterate stmts =
                let do changed := false
                    do errors := []
                    do ignore (checkStmts topScopeId (pushBlock IniEnv.empty stmts) stmts)
                in if !changed
                   then iterate stmts
                   else ()
                end
        in iterate stmts
         ; case !errors
           of [] => Either.Right ()
            | errs => Either.Left (Vector.fromList (List.rev errs))
        end
end
