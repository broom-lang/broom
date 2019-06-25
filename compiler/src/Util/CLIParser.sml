structure CLIParser :> sig
    structure FlagSpecs: ORD_MAP where type Key.ord_key = string
    structure Flaggeds: ORD_MAP where type Key.ord_key = string
    datatype flag_arity = Nullary | Unary
    type flag_specs = flag_arity FlagSpecs.map
    type flaggeds = string option Flaggeds.map
    type positionals = string list

    val parser: flag_specs -> string list -> (string list, flaggeds * positionals) Either.t
end = struct
    structure FlagSpecs = String.SortedMap
    structure Flaggeds = String.SortedMap
    val op|> = Fn.|>

    datatype flag_arity = Nullary | Unary
    type flag_specs = flag_arity FlagSpecs.map
    type flaggeds = string option Flaggeds.map
    type positionals = string list

    datatype token = ShortFlag of string | LongFlag of string | String of string

    fun lexArg arg =
        let val len = String.size arg
        in if len = 0
           then [String arg]
           else case String.sub (arg, 0)
                of #"-" =>
                    if len = 1
                    then [ShortFlag ""]
                    else (case String.sub (arg, 1)
                          of #"-" => [LongFlag (String.extract (arg, 2, NONE))]
                           | _ => String.extract (arg, 1, NONE)
                                      |> String.explode
                                      |> List.map (ShortFlag o String.str))
                 | _ => [String arg]
        end

    val rec lex =
        fn arg :: argv => lexArg arg @ lex argv
         | [] => []

    fun parser flagSpecs argv =
        let val flaggeds = ref Flaggeds.empty
            fun insertFlagged k v = flaggeds := Flaggeds.insert (!flaggeds, k, v)
            val positionals = ref []
            fun insertPositional arg = positionals := arg :: !positionals
            fun buildPositionals () = List.rev (!positionals)
            fun resetPositionals () = positionals := []
            val errors = List.Builder.new ()
            val insertError = List.Builder.pushBack errors
            
            val rec parse =
                fn (ShortFlag f | LongFlag f) :: tokens =>
                    let val tokens = parseFlag f tokens
                    in parse tokens
                    end
                 | tokens as (String _ :: _) =>
                    let val rec parsePositionals =
                            fn String arg :: tokens =>
                                ( insertPositional arg
                                ; parsePositionals tokens )
                             | tokens as (_ :: _) =>
                                let val orphans = buildPositionals ()
                                    do resetPositionals ()
                                in insertError ("Misplaced arguments: " ^ String.concatWith ", " orphans)
                                 ; parse tokens
                                end
                             | [] => ()
                    in parsePositionals tokens
                    end
                 | [] => ()
            
            and parseFlag =
                fn f => fn tokens =>
                    case FlagSpecs.find (flagSpecs, f)
                    of SOME Nullary => (insertFlagged f NONE; tokens)
                     | SOME Unary =>
                        (case tokens
                         of ShortFlag _ :: _ | LongFlag _ :: _ | [] =>
                             ( insertError ("Missing argument for flag " ^ f)
                             ; tokens )
                          | String s :: tokens => (insertFlagged f (SOME s); tokens))
                     | NONE => (insertError ("Unknown flag " ^ f); tokens)

            do parse (lex argv)
        in case List.Builder.build errors
           of [] => Either.Right (!flaggeds, buildPositionals ())
            | errors as (_ :: _) => Either.Left errors
        end
end

