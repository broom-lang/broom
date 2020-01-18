structure WellFounded :> sig
    structure FAst : sig
        structure Term : FAST_TERM
            where type expr = FAst.Term.expr
            where type stmt = FAst.Term.stmt
            where type Type.sv = FAst.Type.sv
    end

    datatype error = ReadUninitialized of Pos.span * Name.t option * Name.t
    
    val errorToDoc : Pos.sourcemap -> error -> PPrint.t

    val elaborate : FAst.Term.program -> (error vector, FAst.Term.program) Either.t
end = struct
    structure FAst = FAst
    structure FTerm = FAst.Term
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

        (* val toDoc : t -> PPrint.t *)
        val compare : t * t -> order
    end = struct
        type t = FTerm.def
        type ord_key = t

        (* val toDoc = FTerm.defToDoc Fn.undefined *)

        fun compare ({id, ...}: t, {id = id', ...}: t) =
            DefId.compare (id, id')
    end

    structure Support = struct
        structure Super = BinarySetFn(Def)
        open Super
(*
        fun toDoc names =
            names
            |> toList
            |> Vector.fromList
            |> Vector.map Def.toDoc
            |> PPrint.punctuate (text "," <> space)
            |> PPrint.braces
*)
    end

    datatype typ
        = Closure of Support.set * typ
        | Record of typ
        | RowExt of {field : Name.t * typ, ext : typ}
        | EmptyRow
        | Scalar
        | Unknown

(*
    val rec typToDoc =
        fn Closure (support, codomain) =>
            text "_" <+> text "->" <+> Support.toDoc support
                <+> typToDoc codomain
         | Record row => PPrint.braces (typToDoc row)
         | (row as RowExt _ | row as EmptyRow) => rowToDoc row
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
*)

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

    fun withoutField (RowExt {ext, field = field as (label, _)}) label' =
        if label = label'
        then SOME ext
        else Option.map (fn ext => RowExt {ext, field})
                        (withoutField ext label')

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
         | (typ as EmptyRow | typ as Scalar | typ as Unknown) =>
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
         | (typ, typ') => raise Fail "unreachable"

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
                     | (MatchFrame _ | FnFrame _) :: frames => init frames
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

    fun checkProgram {typeFns = _, code, sourcemap = _} =
        let val env = Env.new ()
            val changed = ref false
            val errors = ref []
            fun error err = errors := err :: !errors
            
            fun checkExpr ini ctx (Fn (_, {id, ...}, _, body)) =
                let val ini = IniEnv.pushFn ini ctx id
                    val (codomain, support) = checkExpr ini ctx body
                in case ctx
                   of Escaping => (Closure (Support.empty, codomain), support)
                    | Naming => (Closure (support, codomain), Support.empty)
                end

              | checkExpr ini ctx (TFn (_, _, body)) = checkExpr ini ctx body

              | checkExpr ini ctx (Letrec letrec) = checkLetrec ini ctx letrec

              | checkExpr ini ctx (Let (_, stmts, body)) =
                let val (ini, stmtsSupport) = checkStmts ini stmts
                    val (typ, bodySupport) = checkExpr ini ctx body
                in (typ, Support.union (stmtsSupport, bodySupport))
                end

              | checkExpr ini ctx (Match (_, _, matchee, clauses)) =
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

              | checkExpr ini ctx (App (_, _, {callee, arg})) =
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

              | checkExpr ini ctx (TApp (_, _, {callee, args = _})) = checkExpr ini ctx callee

              | checkExpr ini ctx (PrimApp (_, _, _, _, args)) =
                ( Unknown
                , Vector.foldl (fn (arg, support) =>
                                    let val (_, argSupport) = checkExpr ini ctx arg
                                    in Support.union (support, argSupport)
                                    end)
                               Support.empty args )

              | checkExpr ini ctx (With (_, _, {base, field = (label, fieldExpr)})) =
                let val ((Record base | base as Scalar), baseSupport) = checkExpr ini ctx base
                    val (fieldTyp, fieldSupport) = checkExpr ini ctx fieldExpr
                in ( Record (withField base (label, fieldTyp))
                   , Support.union (baseSupport, fieldSupport) )
                end

              | checkExpr ini ctx (Where (_, _, {base, field = (label, fieldExpr)})) =
                let val ((Record base | base as Scalar), baseSupport) = checkExpr ini ctx base
                    val (fieldTyp, fieldSupport) = checkExpr ini ctx fieldExpr
                in ( Record (valOf (whereField base (label, fieldTyp)))
                   , Support.union (baseSupport, fieldSupport) )
                end

              | checkExpr ini ctx (Without (_, _, {base, field})) =
                let val ((Record base | base as Scalar), baseSupport) = checkExpr ini ctx base
                in (Record (valOf (withoutField base field)), baseSupport)
                end

              | checkExpr ini ctx (Field (_, _, expr, label)) =
                let val (recTyp, support) = checkExpr ini ctx expr
                in ( case recTyp
                     of RowExt _ => valOf (rowField recTyp label)
                      | _ => Unknown
                   , support )
                end

              | checkExpr ini ctx (Use (pos, def as {id, var, ...})) =
                let fun access ini via (def as {id, var, ...}) =
                        case IniEnv.access ini id
                        of (Delayed Initialized | Instant Initialized) => (* ok unsupported: *)
                            Support.empty
                         | Delayed Uninitialized => (* ok with support: *)
                            Support.singleton def
                         | Instant Uninitialized => (* error: *)
                            ( error (ReadUninitialized (pos, via, var))
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

              | checkExpr ini ctx (Cast (_, _, expr, _)) = checkExpr ini ctx expr

              | checkExpr ini ctx (EmptyRecord _ | Type _ | Const _) = (Scalar, Support.empty)

            and pushBlock ini stmts =
                let val ids =
                        Vector.foldl (fn (Axiom _, ids) => ids
                                       | (Val (_, {id, ...}, _), ids) => id :: ids
                                       | (Expr _, ids) => ids)
                                     [] stmts
                in IniEnv.pushBlock ini ids
                end

            and checkDefns ini stmts =
                Vector.foldl (fn (stmt, support) =>
                                  Support.union (support, checkDefn ini stmt))
                             Support.empty stmts

            and checkDefn ini =
                fn Axiom _ => Support.empty
                 | Val (_, {id, typ = _, ...}, expr) =>
                    let val (typ, support) = checkExpr ini Naming expr
                        val refineChanged = Env.refine env id typ
                        do changed := (!changed orelse refineChanged)
                        do IniEnv.initialize ini id
                    in support
                    end
                 | Expr expr => #2 (checkExpr ini Escaping expr)

            and checkLetrec ini ctx (pos, stmts, body) =
                let val ini = pushBlock ini (Vector1.toVector stmts)
                    val stmtsSupport = checkDefns ini (Vector1.toVector stmts)
                    val (typ, bodySupport) = checkExpr ini ctx body
                in (typ, Support.union (stmtsSupport, bodySupport))
                end

            and checkStmts ini stmts =
                Vector1.foldl (fn (stmt, (ini, support)) =>
                                   let val (ini, stmtSupport) = checkStmt ini stmt
                                   in (ini, Support.union (support, stmtSupport))
                                   end)
                              (ini, Support.empty) stmts

            and checkStmt ini =
                fn Axiom _ => (ini, Support.empty)
                 | Val (_, {id, ...}, expr) =>
                    let val (typ, support) = checkExpr ini Naming expr
                        val refineChanged = Env.refine env id typ
                        do changed := (!changed orelse refineChanged)
                        val ini = IniEnv.pushMatch ini id
                    in (ini, support)
                    end
                 | Expr expr => (ini, #2 (checkExpr ini Escaping expr))

            and checkClause ini ctx {pattern, body} =
                let val ini = checkPattern ini ctx pattern
                in checkExpr ini ctx body
                end

            and checkPattern ini ctx =
                fn Def (_, {id, ...}) => IniEnv.pushMatch ini id
                 | AnyP _ => ini
                 | ConstP _ => ini

            fun iterate code =
                let do changed := false
                    do errors := []
                    do ignore (checkLetrec IniEnv.empty Escaping code)
                in if !changed
                   then iterate code
                   else ()
                end
        in iterate code
         ; case !errors
           of [] => Either.Right env
            | errs => Either.Left (Vector.fromList (List.rev errs))
        end

    fun emit env {typeFns, code, sourcemap} =
        let val boxDefs = DefId.HashTable.mkTable (0, Subscript)

            fun emitExpr ini ctx (Fn (pos, def as {id, ...}, arr, body)) =
                let val ini = IniEnv.pushFn ini ctx id
                in Fn (pos, def, arr, emitExpr ini ctx body)
                end

              | emitExpr ini ctx (TFn (pos, params, body)) = TFn (pos, params, emitExpr ini ctx body)

              | emitExpr ini ctx (Letrec letrec) = Let (emitLetrec ini ctx letrec)

              | emitExpr ini ctx (Let (pos, stmts, body)) =
                let val stmts = emitStmts ini stmts
                    val body = emitExpr ini ctx body
                in Let (pos, stmts, body)
                end

              | emitExpr ini ctx (Match (pos, t, matchee, clauses)) =
                let val matchee = emitExpr ini ctx matchee
                    val clauses = Vector.map (emitClause ini ctx) clauses
                in Match (pos, t, matchee, clauses)
                end

              | emitExpr ini ctx (App (pos, t, {callee, arg})) =
                App (pos, t, {callee = emitExpr ini Escaping callee, arg = emitExpr ini Escaping arg})

              | emitExpr ini ctx (TApp (pos, t, {callee, args})) =
                TApp (pos, t, {callee = emitExpr ini ctx callee, args})

              | emitExpr ini ctx (PrimApp (pos, t, opn, targs, args)) =
                PrimApp (pos, t, opn, targs, Vector.map (emitExpr ini ctx) args)

              | emitExpr ini ctx (With (pos, t, {base, field = (label, fieldExpr)})) =
                With (pos, t, {base = emitExpr ini ctx base, field = (label, emitExpr ini ctx fieldExpr)})

              | emitExpr ini ctx (Where (pos, t, {base, field = (label, fieldExpr)})) =
                Where (pos, t, {base = emitExpr ini ctx base, field = (label, emitExpr ini ctx fieldExpr)})

              | emitExpr ini ctx (Without (pos, t, {base, field})) =
                Without (pos, t, {base = emitExpr ini ctx base, field})

              | emitExpr ini ctx (Field (pos, t, expr, label)) =
                Field (pos, t, emitExpr ini ctx expr, label)

              | emitExpr ini ctx (expr as Use (pos, def as {pos = defPos, id, typ, ...})) =
                (case IniEnv.access ini id
                 of (Delayed Initialized | Instant Initialized) => expr
                  | Delayed Uninitialized =>
                     let val boxDef = { pos = defPos, id = DefId.fresh (), var = Name.fresh ()
                                      , typ = FTypeBase.App { callee = FTypeBase.Prim PrimType.Box
                                                            , args = Vector1.singleton typ } }
                     in DefId.HashTable.insert boxDefs (id, (typ, boxDef))
                      ; PrimApp (pos, typ, Primop.BoxGet, #[typ], #[Use (pos, boxDef)])
                     end
                  | Instant Uninitialized => raise Fail "unreachable")

              | emitExpr ini ctx (Cast (pos, t, expr, co)) =
                Cast (pos, t, emitExpr ini ctx expr, co)

              | emitExpr ini ctx (expr as (EmptyRecord _ | Type _ | Const _)) = expr

            and pushBlock ini stmts =
                let val ids =
                        Vector.foldl (fn (Axiom _, ids) => ids
                                       | (Val (_, {id, ...}, _), ids) => id :: ids
                                       | (Expr _, ids) => ids)
                                     [] stmts
                in IniEnv.pushBlock ini ids
                end

            and emitDefns ini stmts = VectorExt.flatMap (emitDefn ini) stmts

            and emitDefn ini =
                fn defn as Axiom _ => #[defn]
                 | Val (pos, def as {id, ...}, expr) =>
                    let val expr = emitExpr ini Naming expr
                        do IniEnv.initialize ini id
                    in case DefId.HashTable.find boxDefs id
                       of SOME (contentType, boxDef) =>
                           #[ Val (pos, def, expr)
                            , Expr (PrimApp ( pos, FTypeBase.Record FTypeBase.EmptyRow
                                            , Primop.BoxInit, #[contentType]
                                            , #[Use (pos, boxDef), Use (pos, def)] )) ]
                        | NONE => #[Val (pos, def, expr) ]
                    end
                 | Expr expr => #[Expr (emitExpr ini Escaping expr)]

            and emitLetrec ini ctx (pos, stmts, body) =
                let val ini = pushBlock ini (Vector1.toVector stmts)
                    val stmts = valOf (Vector1.fromVector (emitDefns ini (Vector1.toVector stmts)))
                    val body = emitExpr ini ctx body
                    val stmts =
                        case boxAllocs pos (Vector1.toVector stmts)
                        of SOME boxStmts => valOf (Vector1.concat [boxStmts, stmts])
                         | NONE => stmts
                in (pos, stmts, body)
                end

            and emitStmts ini stmts =
                Vector1.foldl (fn (stmt, (ini, revStmts)) =>
                                   let val (ini, stmt) = emitStmt ini stmt
                                   in (ini, stmt :: revStmts)
                                   end)
                              (ini, []) stmts
                |> #2
                |> List.rev
                |> Vector1.fromList
                |> valOf

            and emitStmt ini =
                fn stmt as Axiom _ => (ini, stmt)
                 | Val (pos, def as {id, ...}, expr) =>
                    let val expr = emitExpr ini Naming expr
                        val ini = IniEnv.pushMatch ini id
                    in (ini, Val (pos, def, expr))
                    end
                 | Expr expr => (ini, Expr (emitExpr ini Escaping expr))

            and emitClause ini ctx {pattern, body} =
                let val (ini, pattern) = emitPattern ini ctx pattern
                in {pattern, body = emitExpr ini ctx body}
                end

            and emitPattern ini ctx =
                fn pat as Def (_, {id, ...}) => (IniEnv.pushMatch ini id, pat)
                 | pat as AnyP _ => (ini, pat)
                 | pat as ConstP _ => (ini, pat)

            and boxAllocs pos stmts =
                let val revBoxStmts =
                        Vector.foldl (fn (Val (_, {id, ...}, _), revBoxStmts) =>
                                          (case DefId.HashTable.find boxDefs id
                                           of SOME (typ, def as {typ = boxTyp, ...}) =>
                                               Val (pos, def, PrimApp (pos, boxTyp, Primop.BoxNew, #[typ], #[]))
                                               :: revBoxStmts
                                            | NONE => revBoxStmts)
                                       | ((Axiom _ | Expr _), revBoxStmts) => revBoxStmts)
                                     [] stmts
                in revBoxStmts |> List.rev |> Vector1.fromList
                end
           
            val code = emitLetrec IniEnv.empty Escaping code
        in {typeFns, code, sourcemap}
        end

    fun elaborate program =
        Either.map (fn ini => emit ini program)
                   (checkProgram program)
end

