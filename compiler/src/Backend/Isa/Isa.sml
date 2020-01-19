signature ISA_OPER = sig
    type def
    type t

    val move : def -> t
    val stackLoad : def -> int -> t (* HACK: need to pass stack pointer *)
    val stackStore : def -> int -> def -> t (* HACK: need to pass stack pointer *)

    val toDoc : t -> PPrint.t
    val foldDefs : (def * 'a -> 'a) -> 'a -> t -> 'a
    val appLabels : (Label.t -> unit) -> t -> unit
end

signature ISA_TRANSFER = sig
    type def
    type t

    val toDoc : t -> PPrint.t
    val isReturn : t -> bool
    val foldDefs : (def * 'a -> 'a) -> 'a -> t -> 'a
    val foldLabels : (Label.t * 'a -> 'a) -> 'a -> t -> 'a
    val appLabels : (Label.t -> unit) -> t -> unit
end

signature INSTRUCTIONS = sig
    type def

    val registerSize : int

    structure Oper : ISA_OPER where type def = def

    structure Transfer : ISA_TRANSFER where type def = def
end

signature ISA = sig
    type def
    type loc
    type oper
    type transfer

    structure Register : REGISTER where type t = def
    structure Location : REGISTER where type t = loc

    structure Instrs : INSTRUCTIONS
        where type def = def
        where type Oper.t = oper
        where type Transfer.t = transfer

    structure Stmt : sig
        datatype t
            = Def of def * oper
            | Eff of oper

        val toDoc : t -> PPrint.t
        val appLabels : (Label.t -> unit) -> t -> unit
    end

    structure Transfer : ISA_TRANSFER where type t = transfer

    structure Cont : sig
        type t = { name : Name.t option
                 , cconv : CallingConvention.t option
                 , params : loc vector
                 , stmts : Stmt.t vector
                 , transfer : Transfer.t }

        val toDoc : Label.t * t -> PPrint.t

        structure Builder : sig
            type builder

            val new : {name : Name.t option, cconv : CallingConvention.t option, argc : int} -> builder
            val setParam : builder -> int -> loc -> unit
            val insertStmt : builder -> Stmt.t -> unit
            val setTransfer : builder -> Transfer.t -> unit
            val build : builder -> t
        end
    end

    structure Program : sig
        type t = {conts : Cont.t Label.HashMap.t, main : Label.t}

        val toDoc : t -> PPrint.t

        structure Builder : sig
            type builder

            val new : unit -> builder
            val createCont : builder -> Label.t
                -> {name : Name.t option, cconv : CallingConvention.t option, argc : int} -> unit
            val setParam : builder -> Label.t -> int -> loc -> unit
            val insertStmt : builder -> Label.t -> Stmt.t -> unit
            val setTransfer : builder -> Label.t -> Transfer.t -> unit
            val build : builder -> Label.t -> t
        end
    end
end

functor IsaFn (Args : sig
    structure Register : REGISTER
    structure Location : REGISTER
    structure Instrs : INSTRUCTIONS where type def = Register.t
end) :> ISA
    where type def = Args.Register.t
    where type loc = Args.Location.t
    where type oper = Args.Instrs.Oper.t
    where type transfer = Args.Instrs.Transfer.t
= struct
    structure Register = Args.Register
    structure Location = Args.Location
    structure Instrs = Args.Instrs
    structure Oper = Instrs.Oper

    type def = Register.t
    type loc = Location.t
    type oper = Oper.t
    type transfer = Args.Instrs.Transfer.t

    val text = PPrint.text
    val comma = PPrint.comma
    val parens = PPrint.parens
    val space = PPrint.space
    val newline = PPrint.newline
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>
    val punctuate = PPrint.punctuate
    val nest = PPrint.nest

    structure Stmt = struct
        datatype t
            = Def of def * oper
            | Eff of oper

        val toDoc =
            fn Def (reg, oper) => Register.toDoc reg <+> text "=" <+> Oper.toDoc oper
             | Eff oper => Oper.toDoc oper

        fun appLabels f =
            fn (Def (_, oper) | Eff oper) => Oper.appLabels f oper
    end

    structure Transfer = Args.Instrs.Transfer

    structure Cont = struct
        type t = { name : Name.t option
                 , cconv : CallingConvention.t option
                 , params : loc vector
                 , stmts : Stmt.t vector
                 , transfer : Transfer.t }

        fun toDoc (label, {name, cconv, params, stmts, transfer}) =
            text "fun"
            <> (case cconv
                of SOME cconv => space <> CallingConvention.toDoc cconv
                 | NONE => PPrint.empty)
            <+> Label.toDoc label
            <+> parens (punctuate (comma <> space) (Vector.map Location.toDoc params)) <+> text "="
            <> nest 4 (newline <> punctuate newline (Vector.map Stmt.toDoc stmts)
                       <++> Transfer.toDoc transfer)

        structure Builder = struct
            type builder = { name : Name.t option, cconv : CallingConvention.t option
                           , params : loc option array
                           , stmts : Stmt.t list ref
                           , transfer : Transfer.t option ref }

            fun new {name, cconv, argc} =
                { name, cconv
                , params = Array.tabulate (argc, Fn.constantly NONE)
                , stmts = ref [], transfer = ref NONE }

            fun setParam ({params, ...} : builder) i loc = Array.update (params, i, SOME loc)

            fun insertStmt ({stmts, ...} : builder) stmt = stmts := stmt :: !stmts

            fun setTransfer ({transfer, ...} : builder) v = transfer := SOME v

            fun build {name, cconv, params, stmts, transfer} =
                { name, cconv
                , params = Vector.map valOf (Array.vector params)
                , stmts = Vector.fromList (List.rev (!stmts))
                , transfer = valOf (!transfer) }
        end
    end

    structure Program = struct
        structure LabelMap = Label.HashMap

        type t = {conts : Cont.t LabelMap.t, main : Label.t}

        fun toDoc {conts, main} =
            LabelMap.fold (fn (kv, acc) => acc <++> newline <> Cont.toDoc kv)
                          PPrint.empty conts
            <++> newline <++> text "entry" <+> Label.toDoc main

        structure Builder = struct
            type builder = Cont.Builder.builder LabelMap.t ref

            fun new () = ref LabelMap.empty

            fun createCont builder label creation =
                builder := LabelMap.insert (!builder) (label, Cont.Builder.new creation)

            fun setParam (ref conts) label i loc =
                Cont.Builder.setParam (LabelMap.lookup conts label) i loc

            fun insertStmt (ref conts) label stmt =
                Cont.Builder.insertStmt (LabelMap.lookup conts label) stmt

            fun setTransfer (ref conts) label transfer =
                Cont.Builder.setTransfer (LabelMap.lookup conts label) transfer

            fun build (ref conts) main =
                {conts = LabelMap.map Cont.Builder.build conts, main}
        end
    end
end

