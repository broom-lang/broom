# TODO

## Next

* [ ] Implement syntax spec

## Later

* [ ] OutsideIn
* [ ] Use null as the ORef layout ptr (?)
* [ ] Correctness: FC Lint
* [ ] Correctness: CPS, Cfg lints
* [ ] Fix https://github.com/nilern/broom/issues/1#issuecomment-658064571
* [ ] Complect lambdas
* [ ] Meta: tasks from notebooks
* [ ] Prevent critical edges
* [ ] #lang `a la Racket
    - With version number and possibly extensions `a la Haskell.
* [ ] Typing: Modular Implicits
* [ ] CPS eval
* [ ] Typing: generativity polymorphism (type family style)
* [ ] (||) = static, (|dyn : {}|) = const (?)
* [ ] Typing: simplify and ensure beta-eta reduction of subtyping coercions
* [ ] Parser: Fix parsing of e.g. `val t: type -> type = ...`
* [ ] Implicits sugar along the lines of 1ML `val id 'a : a -> a` and `fun 'a x = x`. Maybe use `?` as in the implicit calculus paper?
* [ ] Typing: Kind inference (e.g. `pi a => a -> a` = `pi a: type => a -> a`)
* [ ] Typing: Make matches exhaustive
* [ ] UX: Update pprinters
* [ ] Refactor Env
    - [ ] Make FType etc. depend on Env instead of the other way around
    - [ ] Differentiate between V and /\
    - [ ] Don't push a new scope (that never gets popped!) for every REPL line
    - [ ] record pushed typefns and axioms per input program/readline and emit code for them
* [ ] Typing: polymorphic variants
* [ ] Give type errors in terms of the source language (i.e. back-convert to Cst)
* [ ] Optimize: Reduce Vector.of_list calls

## Someday

* [ ] Optimize: parent = NONE and global code motion à la Click
* [ ] Typing: linear types (?)
* [ ] `finally`/ bracket effect
* [ ] Typing: impredicative polymorphism
* [ ] Typing: Recursive modules via elaboration to F_C
* [ ] Configurable associativity and precedence for infix operators
* [ ] Stdlib: Testing framework
* [ ] Tooling: Doc comments and documentation generator
* [ ] Typing: Row typed records and variants
* [ ] Typing: Data via Lens/Prism stuff
* [ ] Typing: GADTs
* [ ] Mid-end: Type erasure / monomorphization (by size class)
* [ ] Backend: Instruction selection
* [ ] Backend: Produce JS
* [ ] Backend: Produce .class files
* [ ] Runtime: broom-gc repo
* [ ] Runtime: Green threads with 'non-blocking' IO (that is, pthread level does not block (as much))
* [ ] Runtime: Continuations and HAMT:s are nice for concurrent, even realtime, GC

## Reference

### Dealing with forward refs after typechecking

- Problem: the below approach won't work with data structures containing fn:s -- including modules!

#### Types
- The elaborated type graph is acyclic, so nothing to do there

#### Values

##### Safety Analysis

Objective: only allow forward references inside functions that are not referenced before all their free variables have been defined

- We walk in the usual "almost eval, but take every branch and descend inside lambdas" style
    * This cannot be folded into the typechecker since that walks more dynamically
- A nominal function is a lambda expression that is immediately bound to a variable; `f = \x . ...` or `f = /\t . ...`.
- A variable is fully initialized when
    * It is a function parameter
    * It is not a nominal function and we have already visited its right hand side
    * It is a nominal function whose every free variable is fully initialized
- A variable use is permissible iff
    * There is at least one nominal lambda contour between it and its def (backward or forward ref, allowed since lambdas suspend the evaluation of the body)
    * The value of the variable is statically known to be fully initialized (backward ref)

##### DAGification

Objective: only allow forward references to functions (removing cycles from the data flow graph since the CPS IR cannot express them)
Approach: Collect nominal functions, hoist them to start of block. Hoist "simple" forward referenced variables before them and "box-convert" non-simple non-lambda forward referenced ones.

Use a variant of the "Fixing Letrec" `letrec*` approach but
- Variables are immutable
- The algorithm needs to insert mutable variables; use `ref` cells instead
    * Maybe the effect system results can be useful? (Maybe not, since it doesn't care about nontermination [inifinite loops / crashing])

---

#### Versio 2

##### Safety analysis spec

* We walk in the usual "almost eval, but take every branch and descend inside lambdas" style
    * This cannot be folded into the typechecker since that walks more dynamically
* A variable depends on another when the other is mentioned in the defining expression
* A variable is fully initialized when
    * All its dependencies are
    * Its definition has already been processed
* A variable use is permissible iff
    * The variable is fully initialized
    * There is at least one \ or /\ contour between the use and def since the use is suspended
        * But this causes a dependency

##### Safety analysis algorithm

* Find out the dependencies of each variable with bottom up pass (like free variable analysis)
* Do the start to end pass, checking the permissibility of each use and keeping the init state of each variable as state, updating at defs

##### DAGification addendum

* We could just box up variables that have fwd uses but using gradual initialization of closures (and records and..?) is more efficient
    * Boxes + hoisting of these allocations + value-flattening might be able to achieve this with out special purpose 'Fixing Letrec' approach?
* What if a continuation captures some of the initialization?!
    * This can be prohibited in the safety analysis as follows: a statement must not have side effects if its scope has already-referenced but still uninitialized variables when it is analyzed
        * Effects that do not capture a continuation at all (ST), never use it (exceptions) or use it at most once (Reader, Coroutine) could be permitted but then we should have affine types available (!)
