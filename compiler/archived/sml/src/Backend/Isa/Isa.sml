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
    type oper
    type t = {pos : Pos.span, oper : oper}

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

    structure Type : CPS_TYPE where type t = Cps.Type.t
    structure Global : CPS_GLOBAL where type t = Cps.Global.t

    structure Instrs : INSTRUCTIONS
        where type def = def
        where type Oper.t = oper
        where type Transfer.oper = transfer

    structure Stmt : sig
        datatype t
            = Def of Pos.span * def * Type.t * oper
            | Eff of Pos.span * oper

        val toDoc : t -> PPrint.t
        val appLabels : (Label.t -> unit) -> t -> unit
    end

    structure Transfer : ISA_TRANSFER where type oper = transfer

    structure Cont : sig
        type t = { pos : Pos.span
                 , name : Name.t option
                 , cconv : CallingConvention.t option
                 , params : (loc option * Type.t) vector
                 , stmts : Stmt.t vector
                 , transfer : Transfer.t }

        val toDoc : Label.t * t -> PPrint.t

        structure Builder : sig
            type builder

            val new : { pos : Pos.span, name : Name.t option, cconv : CallingConvention.t option
                      , paramTypes : Type.t vector } -> builder
            val setParam : builder -> int -> loc -> unit
            val setParams : builder -> (loc option * Type.t) array -> unit
            val getParam : builder -> int -> loc option * Type.t
            val insertStmt : builder -> Stmt.t -> unit
            val setTransfer : builder -> Transfer.t -> unit
            val build : builder -> t
        end
    end

    structure Program : sig
        type t = {globals : Global.t Name.HashMap.t, conts : Cont.t Label.HashMap.t, main : Label.t}

        val toDoc : t -> PPrint.t
        val global : t -> Name.t -> Global.t

        structure Builder : sig
            type builder

            val new : unit -> builder
            val insertGlobal : builder -> Name.t -> Global.t -> unit
            val createCont : builder -> Label.t
                -> { pos : Pos.span, name : Name.t option, cconv : CallingConvention.t option
                   , paramTypes : Type.t vector } -> unit
            val setParam : builder -> Label.t -> int -> loc -> unit
            val setParams : builder -> Label.t -> (loc option * Type.t) array -> unit
            val getParam : builder -> Label.t -> int -> loc option * Type.t
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
    where type transfer = Args.Instrs.Transfer.oper
= struct
    structure Register = Args.Register
    structure Location = Args.Location
    structure Type = Cps.Type
    structure Global = Cps.Global
    structure Instrs = Args.Instrs
    structure Oper = Instrs.Oper

    type def = Register.t
    type loc = Location.t
    type oper = Oper.t
    type transfer = Args.Instrs.Transfer.oper

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
            = Def of Pos.span * def * Type.t * oper
            | Eff of Pos.span * oper

        val toDoc =
            fn Def (_, reg, t, oper) =>
                Register.toDoc reg <+> text ":" <+> Type.toDoc t <+> text "=" <+> Oper.toDoc oper
             | Eff (_, oper) => Oper.toDoc oper

        fun appLabels f =
            fn (Def (_, _, _, oper) | Eff (_, oper)) => Oper.appLabels f oper
    end

    structure Transfer = Args.Instrs.Transfer

    structure Cont = struct
        type t = { pos : Pos.span
                 , name : Name.t option
                 , cconv : CallingConvention.t option
                 , params : (loc option * Type.t) vector
                 , stmts : Stmt.t vector
                 , transfer : Transfer.t }

        fun paramToDoc (loc, typ) =
            (case loc
             of SOME loc => Location.toDoc loc
              | NONE => text "_")
            <+> text ":" <+> Type.toDoc typ

        fun toDoc (label, {pos = _, name, cconv, params, stmts, transfer}) =
            text "fun"
            <> (case cconv
                of SOME cconv => space <> CallingConvention.toDoc cconv
                 | NONE => PPrint.empty)
            <+> Label.toDoc label
            <> (case name
                of SOME name => space <> Name.toDoc name
                 | NONE => PPrint.empty)
            <+> parens (punctuate (comma <> space) (Vector.map paramToDoc params)) <+> text "="
            <> nest 4 (newline <> punctuate newline (Vector.map Stmt.toDoc stmts)
                       <++> Transfer.toDoc transfer)

        structure Builder = struct
            type builder = { pos : Pos.span, name : Name.t option
                           , cconv : CallingConvention.t option
                           , params : (loc option * Type.t) array ref
                           , stmts : Stmt.t list ref
                           , transfer : Transfer.t option ref }

            fun new {pos, name, cconv, paramTypes} =
                { pos, name, cconv
                , params = ref (Array.tabulate ( Vector.length paramTypes
                                               , fn i => (NONE, Vector.sub (paramTypes, i)) ))
                , stmts = ref [], transfer = ref NONE }

            fun setParam ({params, ...} : builder) i loc =
                let val (_, t) = Array.sub (!params, i)
                in Array.update (!params, i, (SOME loc, t))
                end

            fun setParams ({params, ...} : builder) params' = params := params'

            fun getParam ({params, ...} : builder) i = Array.sub (!params, i)

            fun insertStmt ({stmts, ...} : builder) stmt = stmts := stmt :: !stmts

            fun setTransfer ({transfer, ...} : builder) v = transfer := SOME v

            fun build {pos, name, cconv, params, stmts, transfer} =
                { pos, name, cconv
                , params = Array.vector (!params)
                , stmts = Vector.fromList (List.rev (!stmts))
                , transfer = valOf (!transfer) }
        end
    end

    structure Program = struct
        structure LabelMap = Label.HashMap

        type t = {globals : Global.t Name.HashMap.t, conts : Cont.t Label.HashMap.t, main : Label.t}

        fun toDoc {globals, conts, main} =
            let val doc = Name.HashMap.fold (fn ((name, global), acc) =>
                                                 acc <++> newline
                                                 <> text "static" <+> Name.toDoc name <+> text "="
                                                 <+> Global.toDoc global)
                                            PPrint.empty globals
            in LabelMap.fold (fn (kv, acc) => acc <++> newline <> Cont.toDoc kv) doc conts
               <++> newline <++> text "entry" <+> Label.toDoc main
            end

        fun global ({globals, ...} : t) name = Name.HashMap.lookup globals name

        structure Builder = struct
            type builder = { globals : Global.t Name.HashMap.t ref
                           , conts : Cont.Builder.builder LabelMap.t ref }

            fun new () = {globals = ref Name.HashMap.empty, conts = ref LabelMap.empty}

            fun insertGlobal ({globals, ...} : builder) name global =
                globals := Name.HashMap.insert (!globals) (name, global)

            fun createCont ({conts, ...} : builder) label creation =
                conts := LabelMap.insert (!conts) (label, Cont.Builder.new creation)

            fun setParam ({conts = ref conts, ...} : builder) label i loc =
                Cont.Builder.setParam (LabelMap.lookup conts label) i loc

            fun setParams ({conts = ref conts, ...} : builder) label params' =
                Cont.Builder.setParams (LabelMap.lookup conts label) params'

            fun getParam ({conts = ref conts, ...} : builder) label i =
                Cont.Builder.getParam (LabelMap.lookup conts label) i

            fun insertStmt ({conts = ref conts, ...} : builder) label stmt =
                Cont.Builder.insertStmt (LabelMap.lookup conts label) stmt

            fun setTransfer ({conts = ref conts, ...} : builder) label transfer =
                Cont.Builder.setTransfer (LabelMap.lookup conts label) transfer

            fun build {conts = ref conts, globals = ref globals} main =
                {globals, conts = LabelMap.map Cont.Builder.build conts, main}
        end
    end
end

