signature SEQ_ISA = sig
    structure RegIsa : ISA

    structure Program : sig
        type t = { conts : (Label.t * RegIsa.Cont.t) vector
                 , globals : RegIsa.Global.t Name.HashMap.t }


        val toDoc : t -> PPrint.t

        structure Builder : sig
            type builder

            val new : RegIsa.Global.t Name.HashMap.t -> builder
            val appendCont : builder -> Label.t * RegIsa.Cont.t -> unit
            val build : builder -> t
        end
    end
end

functor SeqIsaFn (RegIsa : ISA) :> SEQ_ISA
    where type RegIsa.def = RegIsa.def
    where type RegIsa.loc = RegIsa.loc
    where type RegIsa.oper = RegIsa.oper
    where type RegIsa.Stmt.t = RegIsa.Stmt.t
    where type RegIsa.transfer = RegIsa.transfer
= struct
    structure RegIsa = RegIsa
    structure Global = RegIsa.Global
    structure Cont = RegIsa.Cont

    val text = PPrint.text
    val newline = PPrint.newline
    val op<> = PPrint.<>
    val op<+> = PPrint.<+>
    val op<++> = PPrint.<++>

    structure Program = struct
        type t = { conts : (Label.t * RegIsa.Cont.t) vector
                 , globals : Global.t Name.HashMap.t }

        fun toDoc {globals, conts} =
            let val doc = Name.HashMap.fold (fn ((name, global), acc) =>
                                                 acc <++> newline <> Name.toDoc name <> text ":"
                                                 <++> Global.toDoc global)
                                            PPrint.empty globals
            in Vector.foldl (fn (kv, acc) => acc <++> newline <> Cont.toDoc kv)
                            (doc <++> newline <> text "main:")
                            conts
            end

        structure Builder = struct
            type builder = { globals : Global.t Name.HashMap.t
                           , conts : (Label.t * RegIsa.Cont.t) list ref }

            fun new globals = {globals, conts = ref []}

            fun appendCont ({conts, ...} : builder) kv = conts := kv :: (!conts)

            fun build {globals, conts = ref kvs} =
                {globals, conts = Vector.fromList (List.rev kvs)}
        end
    end
end

