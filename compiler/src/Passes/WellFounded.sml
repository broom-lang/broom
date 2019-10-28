structure WellFounded :> sig
    structure FAst : sig
        structure Term : FAST_TERM
            where type stmt = FixedFAst.Term.stmt
            where type Type.sv = FixedFAst.Type.sv
    end

    datatype error = ReadUninitialized of Pos.span * Name.t option * Name.t
    
    val errorToDoc : Pos.sourcemap -> error -> PPrint.t

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

    datatype error = ReadUninitialized of Pos.span * Name.t option * Name.t

    fun errorToDoc sourcemap (ReadUninitialized (pos, via, name)) =
        text "Error: Cannot prove that" <+> Name.toDoc name
            <+> (case via
                 of SOME via => PPrint.parens (text "via" <+> Name.toDoc via) <> PPrint.space
                  | NONE => PPrint.empty)
            <> text "is initialized in" <+> text (Pos.spanToString sourcemap pos)

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

    datatype context = Escaping | Naming

    datatype state = Uninitialized | Initialized

    datatype access
        = Instant of state
        | Delayed of state

    structure Env :> sig
        type t

        val new : unit -> t
        (* Join the `typ` at the `ScopedId.t` with the `typ`
           and return whether the `typ` was changed by the join: *)
        val refine : t -> DefId.t -> typ -> bool
        val lookup : t -> DefId.t -> typ
    end = struct
        type t = typ DefId.HashTable.hash_table

        fun new () = DefId.HashTable.mkTable (0, Subscript)

        fun lookup env id =
            case DefId.HashTable.find env id
            of SOME typ => typ
             | NONE => Unknown

        fun update env id f =
            let val typ = lookup env id
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

    fun checkProgram (program as {axioms = _, typeFns = _, scope = topScopeId, stmts, sourcemap}) =
        let val env = Env.new ()
            val changed = ref false
            val errors = ref []
            fun error err = errors := err :: !errors
            
            fun checkExpr ini ctx =
                fn Fn (_, {id, ...}, _, body) =>
                    let val ini = IniEnv.pushFn ini ctx id
                        val (codomain, support) = checkExpr ini ctx body
                    in case ctx
                       of Escaping => (Closure (Support.empty, codomain), support)
                        | Naming => (Closure (support, codomain), Support.empty)
                    end
                 | TFn (_, _, body) => checkExpr ini ctx body
                 | Let (_, stmts, body) =>
                    let val ini = pushBlock ini stmts
                        val stmtsSupport = checkStmts ini stmts
                        val (typ, bodySupport) = checkExpr ini ctx body
                    in (typ, Support.union (stmtsSupport, bodySupport))
                    end
                 | Match (_, _, matchee, clauses) =>
                    let val (_, matcheeSupport) = checkExpr ini ctx matchee
                        val (SOME clausesTyp, clausesSupport) =
                            Vector.foldl (fn (clause, (_, support)) =>
                                              let val (clauseTyp, clauseSupport) =
                                                      checkClause ini ctx clause
                                              in ( SOME clauseTyp
                                                 , Support.union (support, clauseSupport) )
                                              end)
                                         (NONE, Support.empty) clauses
                    in (clausesTyp, Support.union (matcheeSupport, clausesSupport))
                    end
                 | App (_, _, {callee, arg}) =>
                    (case checkExpr ini Escaping callee
                     of (Closure (_, codomain), calleeSupport) =>
                         (*       ^-- should be empty because context was `Escaping`. *)
                         let val (_, argSupport) = checkExpr ini Escaping arg
                         in (codomain, Support.union (calleeSupport, argSupport))
                         end
                      | (_, calleeSupport) =>
                         let val (_, argSupport) = checkExpr ini Escaping arg
                         in (Unknown, Support.union (calleeSupport, argSupport))
                         end)
                 | TApp (_, _, {callee, args = _}) => checkExpr ini ctx callee
                 | With (_, _, {base, field = (label, fieldExpr)}) =>
                    let val (Record base, baseSupport) = checkExpr ini ctx base
                        val (fieldTyp, fieldSupport) = checkExpr ini ctx fieldExpr
                    in ( Record (withField base (label, fieldTyp))
                       , Support.union (baseSupport, fieldSupport) )
                    end
                 | Where (_, _, {base, field = (label, fieldExpr)}) =>
                    let val (Record base, baseSupport) = checkExpr ini ctx base
                        val (fieldTyp, fieldSupport) = checkExpr ini ctx fieldExpr
                    in ( Record (valOf (whereField base (label, fieldTyp)))
                       , Support.union (baseSupport, fieldSupport) )
                    end
                 | Field (_, _, expr, label) =>
                    let val (recTyp, support) = checkExpr ini ctx expr
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
                 | Cast (_, _, expr, _) => checkExpr ini ctx expr
                 | Type _ | Const _ => (Scalar, Support.empty)

            and pushBlock ini stmts =
                let val ids =
                        Vector.foldl (fn (Axiom _, ids) => ids
                                       | (Val (_, {id, ...}, _), ids) => id :: ids
                                       | (Expr _, ids) => ids)
                                     [] stmts
                in IniEnv.pushBlock ini ids
                end

            and checkStmts ini stmts =
                Vector.foldl (fn (stmt, support) =>
                                  Support.union (support, checkStmt ini stmt))
                             Support.empty stmts

            and checkStmt ini =
                fn Axiom _ => Support.empty
                 | Val (_, {id, typ = _, ...}, expr) =>
                    let val (typ, support) = checkExpr ini Naming expr
                        val refineChanged = Env.refine env id typ
                        do changed := (!changed orelse refineChanged)
                        do IniEnv.initialize ini id
                    in support
                    end
                 | Expr expr => #2 (checkExpr ini Escaping expr)

            and checkClause ini ctx {pattern, body} =
                let val ini = checkPattern ini ctx pattern
                in checkExpr ini ctx body
                end

            and checkPattern ini ctx =
                fn Def (_, {id, ...}) => IniEnv.pushMatch ini id
                 | ConstP _ => ini

            fun iterate stmts =
                let do changed := false
                    do errors := []
                    do ignore (checkStmts (pushBlock IniEnv.empty stmts) stmts)
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

