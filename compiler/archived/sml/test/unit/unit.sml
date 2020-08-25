val status =
    ( TestWord32.runTests ()
    ; TestHashMap.runTests ()
    ; TestTrictor.runTests ()
    ; TestTwobitMap.runTests ()
    ; OS.Process.success )
    handle TestTrictor.Assert.AssertFailed msg =>
            ( TextIO.output (TextIO.stdErr, "Assert failed: " ^ msg ^ "\n")
            ; OS.Process.failure )
         | TestWord32.Assert.AssertFailed msg =>
            ( TextIO.output (TextIO.stdErr, "Assert failed: " ^ msg ^ "\n")
            ; OS.Process.failure )
         | TestHashMap.Assert.AssertFailed msg =>
            ( TextIO.output (TextIO.stdErr, "Assert failed: " ^ msg ^ "\n")
            ; OS.Process.failure )
         | TestTwobitMap.Assert.AssertFailed msg =>
            ( TextIO.output (TextIO.stdErr, "Assert failed: " ^ msg ^ "\n")
            ; OS.Process.failure )

do OS.Process.exit status

