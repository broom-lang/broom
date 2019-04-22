structure Main :> sig
    val main: string list -> unit
end = struct
    val parseArgs =
        fn [] => {debug = false, instream = TextIO.stdIn, name = "<stdin>"}
         | ["--debug"] => {debug = true, instream = TextIO.stdIn, name = "<stdin>"}
         | [name] => {debug = false, instream = TextIO.openIn name, name = name}
         | ["--debug", name] => {debug = true, instream = TextIO.openIn name, name = name}

    fun main args = Parser.parse (parseArgs args)
end

val _ = Main.main (CommandLine.arguments ())

