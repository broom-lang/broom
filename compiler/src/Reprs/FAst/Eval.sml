structure FAstEval :> sig
    structure Value: sig
        type t

        val toString: t -> string
    end

    type toplevel = Value.t NameHashTable.hash_table

    val newToplevel: unit -> toplevel
    val interpret: toplevel -> FixedFAst.Term.stmt -> Value.t
end = struct
    structure FType = FixedFAst.Type
    structure FTerm = FixedFAst.Term
    datatype expr = datatype FTerm.expr
    datatype stmt = datatype FTerm.stmt
    datatype pat = datatype FTerm.pat
    type clause = FTerm.clause

    datatype value = Closure of env * Name.t * expr
                   | Thunk of env * expr
                   | Record of value NameHashTable.hash_table
                   | Array of value array
                   | TypeWitness of FType.concr
                   | Int of int
                   | Bool of bool
                   | Uninitialized

    and env = Toplevel of bindings
            | FnScope of env * Name.t * value
            | BlockScope of env * bindings
            | PatternScope of env * Name.t * value

    withtype bindings = value NameHashTable.hash_table

    type toplevel = bindings

    datatype frame = Def of env * Name.t
                   | Callee of env * expr
                   | Arg of value
                   | PrimArg of env * Primop.t * expr VectorSlice.slice * value list
                   | Forcee
                   | BlockCont of env * stmt Vector1.Slice.slice * expr
                   | Branches of env * clause VectorSlice.slice
                   | Extension of env * (Name.t * expr)
                   | Extend of env * value * Name.t
                   | Exclude of env * Name.t
                   | GetField of Name.t

    structure Value = struct
        val op|> = Fn.|>
        val op<> = PPrint.<>
        val op<+> = PPrint.<+>
        val text = PPrint.text

        type t = value

        val emptyRecord = Record (NameHashTable.mkTable (0, Subscript))

        val rec toDoc =
            fn Closure _ => text "#<fn>"
             | Thunk _ => text "#<Fn>"
             | Record fields =>
                let val fieldDocs = fields
                                  |> NameHashTable.listItemsi
                                  |> Vector.fromList
                                  |> Vector.map fieldToDoc
                in PPrint.braces (PPrint.punctuate (text "," <> PPrint.space)
                                                   fieldDocs)
                end
             | Array vs =>
                PPrint.brackets (PPrint.punctuate (text "," <> PPrint.space)
                                                  (Array.vector vs
                                                  |> Vector.map toDoc))
             | TypeWitness t =>
                PPrint.brackets (text "=" <+> FType.Concr.toDoc () t)
             | Int n => text (Int.toString n)
             | Bool true => text "True"
             | Bool false => text "False"
             | Uninitialized => text "#<uninitialized>"
        and fieldToDoc = fn (label, v) => Name.toDoc label <+> text "=" <+> toDoc v

        val toString = PPrint.pretty 80 o toDoc
    end

    fun initField fields label value = NameHashTable.insert fields (label, value)

    fun splat fields ext =
        case ext
        of Record ext =>
            NameHashTable.appi (fn (label, v) =>
                                    if NameHashTable.inDomain fields label
                                    then ()
                                    else NameHashTable.insert fields (label, v))
                               ext
         | _ => raise Fail "unreachable"

    fun getField record label =
        case record
        of Record fields => NameHashTable.lookup fields label
         | _ => raise Fail "unreachable"

    fun enter env var value = FnScope (env, var, value)

    fun enterBlock env = BlockScope (env, NameHashTable.mkTable (0, Subscript))

    fun define env var value =
        case env
        of Toplevel bindings | BlockScope (_, bindings) =>
            NameHashTable.insert bindings (var, value)
         | FnScope _ | PatternScope _ => raise Fail "unreachable"

    fun lookup env var =
        case env
        of Toplevel toplevel => NameHashTable.lookup toplevel var
         | FnScope (parent, var', value) | PatternScope (parent, var', value) =>
            if var = var'
            then value
            else lookup parent var
         | BlockScope (parent, bindings) =>
            (case NameHashTable.find bindings var
             of SOME value => value
              | NONE => lookup parent var)

    val constValue =
        fn Const.Int n => Int n
         | Const.Bool b => Bool b

    fun eval env cont =
        fn Fn (_, {var, ...}, _, body) => continue cont (Closure (env, var, body))
         | TFn (_, _, body) => continue cont (Thunk (env, body))
         | App (_, _, {callee, arg}) => eval env (Callee (env, arg) :: cont) callee
         | TApp (_, _, {callee, ...}) => eval env (Forcee :: cont) callee
         | PrimApp (_, _, opn, _, args) =>
            (case Vector.uncons args
             of SOME (arg, args) => eval env (PrimArg (env, opn, args, []) :: cont) arg
              | NONE => applyPrim env cont opn #[])
         | EmptyRecord _ => continue cont Value.emptyRecord
         | With (_, _, {base, field}) | Where (_, _, {base, field}) =>
            eval env (Extension (env, field) :: cont) base
         | Without (_, _, {base, field}) => eval env (Exclude (env, field) :: cont) base
         | Let (_, stmts, body) | Letrec (_, stmts, body) =>
            let val env = enterBlock env
                val stmt = Vector1.sub (stmts, 0)
                val stmts = Vector1.Slice.slice (stmts, 1, NONE)
            in exec env (BlockCont (env, stmts, body) :: cont) stmt
            end
         | Match (_, _, matchee, clauses) =>
            eval env (Branches (env, VectorSlice.full clauses) :: cont) matchee
         | Field (_, _, expr, label) => eval env (GetField label :: cont) expr
         | Cast (_, _, expr, _) => eval env cont expr
         | Type (_, t) => continue cont (TypeWitness t)
         | Use (_, {var, ...}) => continue cont (lookup env var)
         | Const (_, c) => continue cont (constValue c)

    and exec env cont =
        fn Val (_, {var, ...}, expr) => eval env (Def (env, var) :: cont) expr
         | Axiom _ => continue cont Value.emptyRecord
         | Expr expr => eval env cont expr

    and apply cont f arg =
        case f
        of Closure (env, var, body) => eval (enter env var arg) cont body
         | _ => raise Fail "unreachable"

    and force cont thunk =
        case thunk
        of Thunk (env, body) => eval env cont body
         | _ => raise Fail "unreachable"

    and applyPrim env cont opn args =
        case opn
        of Primop.IAdd | Primop.ISub | Primop.IMul | Primop.IDiv =>
            (case args
             of #[Int a, Int b] =>
                 let val n =
                         case opn
                         of Primop.IAdd => a + b
                          | Primop.ISub => a - b
                          | Primop.IMul => a * b
                          (*| Primop.IDiv => a / b*)
                 in continue cont (Int n)
                 end)
         | Primop.ArrayT =>
            (case args
             of #[TypeWitness t] =>
                 continue cont (TypeWitness (FType.App { callee = FType.Prim PrimType.Array
                                                       , args = Vector1.singleton t })))
         | Primop.ArrayNew =>
            (case args
             of #[Int count] => continue cont (Array (Array.array (count, Uninitialized))))
         | Primop.ArrayCount =>
            (case args
             of #[Array vs] => continue cont (Int (Array.length vs)))
         | Primop.ArrayGet =>
            (case args
             of #[Array vs, Int i] => continue cont (Array.sub (vs, i)))
         | Primop.ArrayUnsafeSet =>
            (case args
             of #[Array vs, Int i, v] =>
                 ( Array.update (vs, i, v)
                 ; Value.emptyRecord ))

    (* TODO: When user code can run inside patterns, will need to capture position in pattern in cont: *)
    and match env cont clauses value =
        case VectorSlice.uncons clauses
        of SOME (clause, clauses) =>
            let fun matchClause {pattern, body} =
                    case pattern
                    of FTerm.Def (_, {var, ...}) =>
                        let val env = PatternScope (env, var, value)
                        in eval env cont body
                        end
                     | ConstP (_, c) =>
                        (case (constValue c, value)
                         of (Int n, Int nv) =>
                             if n = nv
                             then eval env cont body
                             else match env cont clauses value
                          | (Bool b, Bool nb) =>
                             if b = nb
                             then eval env cont body
                             else match env cont clauses value)
            in matchClause clause
            end
         | NONE => raise Fail ("Missing case for " ^ Value.toString value)

    and continue cont value =
        case cont
        of Def (env, var) :: cont =>
            ( define env var value
            ; continue cont value ) (* `value` is arbitrary but useful for REPL printout. *)
         | Callee (env, arg) :: cont => eval env (Arg value :: cont) arg
         | Arg f :: cont => apply cont f value
         | Forcee :: cont => force cont value
         | PrimArg (env, opn, argExprs, args) :: cont =>
            (case VectorSlice.uncons argExprs
             of SOME (argExpr, argExprs) =>
                 eval env (PrimArg (env, opn, argExprs, value :: args) :: cont) argExpr
              | NONE =>
                 applyPrim env cont opn (Vector.fromList (List.rev (value :: args))))
         | BlockCont (env, stmts, body) :: cont =>
            (case Vector1.Slice.uncons stmts
             of SOME (stmt, stmts) =>
                 exec env (BlockCont (env, stmts, body) :: cont) stmt
              | NONE => eval env cont body)
         | Branches (env, clauses) :: cont => match env cont clauses value
         | Extension (env, (label, fielde)) :: cont =>
            eval env (Extend (env, value, label) :: cont) fielde
         | Extend (env, record, label) :: cont =>
            (case record
             of Record fields =>
                 let val fields = NameHashTable.copy fields
                     do NameHashTable.insert fields (label, value)
                 in continue cont (Record fields)
                 end
              | _ => raise Fail "unreachable")
         | Exclude (env, label) :: cont =>
            (case value
             of Record fields =>
                 let val fields = NameHashTable.copy fields
                     do ignore (NameHashTable.remove fields label)
                 in continue cont (Record fields)
                 end
              | _ => raise Fail "unreachable")
         | GetField label :: cont => continue cont (getField value label)
         | [] => value

    fun newToplevel () = NameHashTable.mkTable (0, Subscript)

    fun interpret toplevel = exec (Toplevel toplevel) []
end

