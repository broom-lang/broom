******************
MLF Type Inference
******************

Based on MLF materials such as Yakobowski's PhD thesis.

My interpretations here are highly likely to contain errors.

===========
Unification
===========

0. Initialize auxiliary data structures:

    * ``let mut mergeds = {}``
    * ``let mut rpo = []``
    * ``let mut parents = {}``
    * ``let mut bindees = {}``
    * ``let s0 = env.current_subst()``

1. Unify the first-order monotype skeletons and build various other things.
   At each step (function activation) two nodes t and t' are unified:

    * Graft if t or t' is ``_|_``.
    * Fail if node shapes are incompatible.
    * Traverse children:
        a. If the step does not graft, recurse through them.
        b. If the step does graft, traverse the grafted node, passing down parent
           and for each descendant t:
        
            * ``parents[t] := parent :: (parents[t] || [])``
            * ``rpo := t :: rpo``

    * ``mergeds[t] := (mergeds[t] || {t}) U {t'}``
    * ``rpo := t :: rpo``

   Since we are collecting ``rpo`` etc., can't skip forward on pointer-equal t and t'.

2. Raise type nodes following ``rpo`` for t1. At each node:

    * ``let binders = {m.binder for m in mergeds[t]}``
    * ``let parents = U {parents[m] for m in mergeds[t]}``
    * ``let binder = lca(rpo, binders U parents)``
    * ``m.binder := binder for m in mergeds[t]``

3. ``let s2 = env.current_subst()``
4. Weaken type nodes following ``rpo`` for t2. At each node:

    * ``let flags = {m.flag for m in mergeds[t]}``
    * ``let flag = Rigid if Rigid in flags else Flex``
    * ``for m in mergeds[t] do m.flag := flag``
    * ``for m in mergeds[t] do bindees[m.binder] := (bindees[m.binder] || {}) U {m}``

4. ``let s4 = env.current_subst()``
5. Traverse t4 (order does not matter this time) and at each step for
   each ``t in bindees[t]``:

   * If ``permission[[s0]t] != Green``:

       * Grafting: fail if ``[s0]t == _|_ && [s4]t != _|_``

   * If ``permission[[s0]t] == Red``:

       * Raising: fail if ``[s0](t.binder) != [s4](t.binder)``

   * If ``permission[[s2]t] == Red``:

       * Weakening: fail if ``[s2](t.flag) != [s4](t.flag)``
       * Merging: fail if ``length bindees[t] > 1``

