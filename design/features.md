# Feature Classification

## MVP

* Row typed records
* Polymorphic variants (not strictly necessary, but nice to reserve syntax)
* Unboxed tuples
* Type proxies (incl. type members for module records)
    - With applicative functors => higher kinded types
* Generative and applicative functors
    - Applicative ones may be very limited, but at least type ctors
* Impredicative higher rank polymorphism
    - Via OutsideIn and out of order solver (a pass)
* Pattern matching
    - Exhaustiveness checking (a pass, after constraint solver)
* Recursive modules
    - Static initialization check (a pass, after patterns check & expansion)
* Row typed effects
* Hardcoded resolution
    - type arguments
    - record field offsets (`lacks` predicates)
* Levity
    - Levity monomorphism restriction
* Special forms (e.g. `let`)
* `_` sugar for tiny lambdas

### But Requires Research

* Type errors in surface syntax
* ADTs
    - Constructors & accessors
        * Lenses & Prisms?
        * Exhaustiveness checking
* Hardcoded resolution
    - deep subtyping
* Singleton types
    - at least of type `type`

## Later

* Clean up and warn about unused code
    - Also warn about unused parameters
* GADTs (necessary for effect handling)
* Custom effect handlers
* Custom patterns (Prisms?)
* Macros

### Serious Research Here

* Functor fixpoints
* Generativity polymorphism
    - And inferring applicative functor types
* General/custom Type Classes / Implicits
    - Naturally, with local instances (but how?)
* Trait Objects (data + evidence, analogoues to existential types)
    - Also for record field offsets

