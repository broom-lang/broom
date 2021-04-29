# Compiler Passes

## Frontend

* Parse
    - Including lexing
* Macroexpand
    - Also hardcoded syntactic sugar expansions
* Typecheck
    - Generate constraints
        * Also emits primop calls for interactive global defs and uses ATM
    - Solve constraints (that weren't solved on the fly)
    - Clean up coercion function and type nodes from Fc tree
* Pattern expansion and coverage checking
    - Needs type information, so after typechecking
* Forward reference implementation and soundness checking
    - Easier without complicated patterns, so after pattern expansion

After this point there are no user errors, only warnings.

* Shrinking reductions
    - Emitting warnings about unused code
    - Can't shrink until all error checking is done
    - Harder to emit good warnings after CPS conversion
        * Also good to reduce the amount of code to CPS-convert

## Middle-end

After this point there are no user errors or warnings, only compiler bugs.

* CPS conversion
* Optimizer
    - Unbox tuples (all of them, thanks to levity in type system)
* Closure conversion (not when compiling to JS)
* Operation scheduling -> CFG

## Backend

* JS emission

