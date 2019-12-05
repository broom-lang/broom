val status =
    ( TestWord32.runTests ()
    ; TestTrictor.runTests ()
    ; OS.Process.success )
    handle TestTrictor.Assert.AssertFailed msg =>
            ( TextIO.output (TextIO.stdErr, "Assert failed: " ^ msg ^ "\n")
            ; OS.Process.failure )
         | TestWord32.Assert.AssertFailed msg =>
            ( TextIO.output (TextIO.stdErr, "Assert failed: " ^ msg ^ "\n")
            ; OS.Process.failure )


do OS.Process.exit status

