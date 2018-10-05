# Type Checking

- [ ] Complete and Easy Bidirectional...
- [ ] Row types for records
- [ ] Row types for effects
- [ ] Modules
- [ ] Monomorphization

# Translation

- [x] Alphatization
- [x] De-`rec` let:s
- [x] CPS conversion
- [ ] cont-stack 'State' xform
- [ ] Expression tree restoration (single-use var inlining)
- [ ] CPS -> JSExpr conversion
- [ ] Cheney on the MTA mini-runtime

# QA

- [ ] Type checkers for every IR
- [ ] Correct by construction (PrimApp is especially bad atm.)
- [ ] Tests (QuickCheck)

# Maybe Later

## Continuation Closure Avoidance

- [ ] Continuation closurification
    * [ ] Functions can be nested; traverse function tree in post order.
    * [ ] Call/escape analysis for continuations
    * [ ] Dominator tree/forest computation a la nilern/complement (start with virtual root
          that has directly-escaping conts as children)
    * [ ] Use-site modification (closure call vs. local jump)
    * [ ] Continuation closure placement (must dominate all use-sites, including
          captures by other continuation closures; bottom up traversal of continuation
          closure dependency tree (dag?), for each closure finding lowest common dominator
          of uses)
    * [ ] Sanity check: defs still dominate uses (i.e. no closure has been hoisted over its
          free variables)

## Output Quality Assurance

- [ ] Avoid generating ternary statements
- [ ] Use newer JS features (let scoping + ReferenceError, TCO) when requested via flag
- [ ] Control structure restoration (see "No More Gotos: Decompilation Using ...")
