- [ ] Alphatization
- [ ] CPS conversion
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
- [ ] Control structure restoration (structural analysis; assume CFG to be a DAG)
- [ ] Expression tree restoration (single-use var inlining)
- [ ] CPS -> JSExpr conversion
- [ ] Cheney on the MTA mini-runtime
