structure FAstEval :> sig
    structure Value: sig
        type t

        val toString: t -> string
    end

    type toplevel = Value.t NameHashTable.hash_table
    type runtime_error = unit

    val newToplevel: unit -> toplevel
    val interpret: toplevel -> FixedFAst.Term.stmt -> (runtime_error, Value.t) Either.t
end = struct
    structure FTerm = FixedFAst.Term
    datatype expr = datatype FTerm.expr
    datatype stmt = datatype FTerm.stmt

    datatype value = Closure of env * Name.t * expr
                   | Thunk of env * expr
                   | Record of value NameHashTable.hash_table
                   | Int of int
                   | Bool of bool
                   | Unit

    and env = Toplevel of bindings
            | FnScope of env * Name.t * value
            | BlockScope of env * bindings

    withtype bindings = value NameHashTable.hash_table

    type toplevel = bindings

    datatype frame = Def of env * Name.t
                   | Callee of env * expr
                   | Arg of value
                   | Forcee
                   | BlockCont of env * stmt VectorSlice.slice * expr
                   | Branch of env * expr * expr
                   | InitField of env * (Name.t * expr) VectorSlice.slice * expr option
                                * value NameHashTable.hash_table * Name.t
                   | Splat of value NameHashTable.hash_table
                   | GetField of Name.t
    
    type cont = frame list

    structure Value = struct
        val op|> = Fn.|>
        val op<> = PPrint.<>
        val op<+> = PPrint.<+>
        val text = PPrint.text

        type t = value

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
             | Int n => text (Int.toString n)
             | Bool true => text "True"
             | Bool false => text "False"
             | Unit => text "()"

        and fieldToDoc = fn (label, v) => Name.toDoc label <+> text "=" <+> toDoc v

        val toString = PPrint.pretty 80 o toDoc
    end

    type runtime_error = unit

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
         | FnScope _ => raise Fail "unreachable"

    fun lookup env var =
        case env
        of Toplevel toplevel => NameHashTable.lookup toplevel var
         | FnScope (parent, var', value) =>
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
        fn Fn (_, {var, ...}, body) => continue cont (Closure (env, var, body))
         | TFn (_, _, body) => continue cont (Thunk (env, body))
         | App (_, _, {callee, arg}) => eval env (Callee (env, arg) :: cont) callee
         | TApp (_, _, {callee, ...}) => eval env (Forcee :: cont) callee
         | Let (_, stmts, body) =>
            (case Vector.uncons stmts
             of SOME (stmt, stmts) =>
                 let val env = enterBlock env
                 in exec env (BlockCont (env, stmts, body) :: cont) stmt
                 end
              | NONE => eval env cont body)
         | If (_, cond, conseq, alt) => eval env (Branch (env, conseq, alt) :: cont) cond
         | Extend (_, _, fields, ext) =>
            (case Vector.uncons fields
             of SOME ((label, expr), fields') =>
                 let val record = NameHashTable.mkTable (Vector.length fields, Subscript)
                 in eval env (InitField (env, fields', ext, record, label) :: cont) expr
                 end
              | NONE =>
                 (case ext
                  of SOME ext => eval env cont ext
                   | NONE => continue cont (Record (NameHashTable.mkTable (0, Subscript)))))
         | Override (_, _, fields, original) =>
            (case Vector.uncons fields
             of SOME ((label, expr), fields') =>
                 let val record = NameHashTable.mkTable (0, Subscript)
                 in eval env (InitField (env, fields', SOME original, record, label) :: cont) expr
                 end
              | NONE => eval env cont original)
         | Field (_, _, expr, label) => eval env (GetField label :: cont) expr
         | Cast (_, _, expr, _) => eval env cont expr
         | Type _ => continue cont Unit
         | Use (_, {var, ...}) => continue cont (lookup env var)
         | Const (_, c) => continue cont (constValue c)

    and exec env cont =
        fn Val (_, {var, ...}, expr) => eval env (Def (env, var) :: cont) expr
         | Expr expr => eval env cont expr

    and apply cont f arg =
        case f
        of Closure (env, var, body) => eval (enter env var arg) cont body
         | _ => raise Fail "unreachable"

    and force cont thunk =
        case thunk
        of Thunk (env, body) => eval env cont body
         | _ => raise Fail "unreachable"

    and continue cont value =
        case cont
        of Def (env, var) :: cont =>
            ( define env var value
            ; continue cont value ) (* `value` is arbitrary but useful for REPL printout. *)
         | Callee (env, arg) :: cont => eval env (Arg value :: cont) arg
         | Arg f :: cont => apply cont f value
         | Forcee :: cont => force cont value
         | BlockCont (env, stmts, body) :: cont =>
            (case VectorSlice.uncons stmts
             of SOME (stmt, stmts) =>
                 exec env (BlockCont (env, stmts, body) :: cont) stmt
              | NONE => eval env cont body)
         | Branch (env, conseq, alt) :: cont =>
            (case value
             of Bool true => eval env cont conseq
              | Bool false => eval env cont alt
              | _ => raise Fail "unreachable")
         | InitField (env, fields, ext, record, label) :: cont =>
            ( initField record label value
            ; case VectorSlice.uncons fields
              of SOME ((label, expr), fields) =>
                  eval env (InitField (env, fields, ext, record, label) :: cont) expr
               | NONE => 
                  (case ext
                   of SOME ext => eval env (Splat record :: cont) ext
                    | NONE => continue cont (Record record)) )
         | Splat record :: cont =>
            ( splat record value
            ; continue cont (Record record) )
         | GetField label :: cont => continue cont (getField value label)
         | [] => value

    fun newToplevel () = NameHashTable.mkTable (0, Subscript)

    fun interpret toplevel = Either.Right o exec (Toplevel toplevel) []
end

