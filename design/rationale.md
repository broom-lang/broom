# Rationale

The ML language family is elegant and solid, but:

## Effortless Recursion

* Recursion should just work, for values and types (as in e.g. Haskell)
  and modules also.

## Module Inference

* Typing out module references for e.g. `Vector.map` is tedious. Modules
  should be inferred when possible (with type classes or implicits).
* Functor instances should be shared automatically (applicative functors,
  OCaml does this but SML does not).

## Effect System

* It should be possible to reason about side effects with types and
  encapsulate them with handlers (effect system). It also turns out that
  this replaces the value restriction and enables inferring applicativity
  (static purity) of functors.

## No Stratification

* All the duplication between core and modules is awkward (first class
  modules).
    - Mixins (MixML, Scala) would be even worse since modules/signatures
      and functor application is at least very similar to values/types
      and function application. Mixin composition is quite different.
* Modules should have pattern matching so that imports don't get verbose
  (imports definitely should not be a big deal).

## Misc

* Operator precedence is just bad compared to Haskell or Scala.

## Stay Simple and Familiar

* MLF and MixML totally eliminate the limitations around higher-ranked
  types and recursive modules but the price in nonstandard complexity
  is high and pervasive for both users and implementors.

