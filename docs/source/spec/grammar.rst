********************
Context-Free Grammar
********************

========
Notation
========

A shorthand notation for separated sequences will be used:

.. math::
    sep(e, s) \rightarrow (e \; (s \; e)^*)? \; s?

A trailing separator is always permitted. This slightly simplifies generating
Broom source code, allows using semicolons like terminators (C-style) instead
of separators (Pascal-style) and can also be used to avoid spurious lines in
version control diffs.

=================
Compilation Units
=================

.. math::
    program &\rightarrow (def \; \textbf{;})^* \; expr \; \textbf{;}?\\
    module &\rightarrow expr \\
    interaction &\rightarrow stmts

A program is like a top level ``let`` expression; a sequence of
semicolon-separated definitions followed by a single entry point expression.

A module file just consists of a single expression. The module expression does
not need to be a record expression or even evaluate to a record; for example a
function can be used to make a parameterized module.

A REPL interaction is like a top level ``do`` expression; a sequence of
semicolon-separated statements.

=====
Terms
=====

-----------
Expressions
-----------

.. math::
    expr \rightarrow annotated

.. math::
    annotated &\rightarrow disjunction \; \textbf{:} \; type \\
        &\quad | \; disjunction

.. math::
    disjunction &\rightarrow disjunction \; \textbf{||} \; conjunction \\
        &\quad | \; conjunction \\
    conjunction &\rightarrow conjunction \; \textbf{&&} \; comparison \\
        &\quad | \; comparison \\
    comparison &\rightarrow additive \; \mathrm{COMPARISON} \; additive \\
        &\quad | \; additive \\
    additive &\rightarrow additive \; \mathrm{ADDITIVE} \; multiplicative \\
        &\quad | \; multiplicative \\
    multiplicative &\rightarrow multiplicative \; \mathrm{MULTIPLICATIVE} \; app \\
        &\quad | \; app

.. math::
    app &\rightarrow app \; projection \\
        &\quad | \; \mathrm{INTRINSIC} \; projection^+ \\
        &\quad | \; projection \\
    projection &\rightarrow projection \; \textbf{.} \; \mathrm{IDENTIFIER} \\
        &\quad | \; projection \; \textbf{.} \; \mathrm{UINT} \\
        &\quad | \; aexpr

.. math::
    aexpr &\rightarrow fn \; | \; fnType \; | \; implicitFnType \\
        &\quad | \; record \; | \; recordType \\
        &\quad | \; tuple \; | \; tupleType \\
        &\quad | \; sumType \; | \; rowType \\
        &\quad | \; parenthesized \\
        &\quad | \; \mathrm{IDENTIFIER} \; | \; \mathrm{WILDCARD} \; | \; \mathrm{LITERAL} \\
    fn &\rightarrow \textbf{[} \; clauses \; \textbf{]} \\
        &\quad | \; \textbf{[} \; stmts \; \textbf{]} \\
    clauses &\rightarrow
        \textbf{|} \\
        &\quad | \; (\textbf{|} \; pat \; \textbf{->} \; expr)^+ \\
        &\quad | \; (\textbf{|} \; pat \; \textbf{=>} \; expr)^+ \\
    fnType &\rightarrow \textbf{[} \; pat \; (\textbf{-!} \; disjunction)? \; \textbf{->} type \; \textbf{]} \\
    implicitFnType &\rightarrow \textbf{[} \; pat \; \textbf{=>} type \; \textbf{]} \\
    record &\rightarrow \textbf{\{} \; stmts \; \textbf{\}} \\
    recordType &\rightarrow \textbf{\{} \; \textbf{:} \; decls \; \textbf{\}} \\
    tuple &\rightarrow \textbf{(} \; tupleExprs \; \textbf{)} \\
    tupleExprs &\rightarrow \textbf{,}?
        \; | \; expr \; \textbf{,}
        \; | \; expr \; (\textbf{,} \; expr)^* \\
    tupleType &\rightarrow \textbf{(} \; \textbf{:} \; types \; \textbf{)} \\
    sumType &\rightarrow \textbf{(} \; \textbf{#} \; decls \; \textbf{)} \\
    rowType &\rightarrow \textbf{(} \; \textbf{|} \; decls \; \textbf{)} \\
    parenthesized &\rightarrow \textbf{(} \; expr \; \textbf{)}

--------
Patterns
--------

.. math::
    pat \rightarrow expr

-----------
Definitions
-----------

.. math::
    def \rightarrow pat \; \textbf{=} \; expr

----------
Statements
----------

.. math::
    stmt &\rightarrow def \; | \; expr \\
    stmts &\rightarrow sep(stmt, \textbf{;})

=====
Types
=====

.. math::
    type &\rightarrow expr \\
    types &\rightarrow sep(type, \textbf{,})

------------
Declarations
------------

.. math::
    decl &\rightarrow def \; | \; disjunction \; \textbf{:} \; type \; | \; disjunction \\
    decls &\rightarrow sep(decl, \textbf{;})

