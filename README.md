# Broom

<img src="Broom_logo.svg" alt="Broom logo" width="120"/>

A programming language with first-class modules and algebraic effects.  Still
very much a work in progress (i.e. not yet usable).

## (Planned) Features

* Functional-first, with strict evaluation
* ML-style module system with higher-order, recursive and first-class modules
    - Records and modules are the same, à la 1ML
    - First-class ML-modules also provide higher-ranked and higher kinded types
        * with impredicative instantiation
    - Modular implicits support ad-hoc polymorphism and type level programming
* Algebraic effects and effect handlers
* Row typed modules, records, polymorphic variants and effects
* Conventional and simplified syntax
    - extensible with procedural hygienic macros
* Optimizing whole-program compilation to Javascript or (later) native code

## (Abstract) Syntax

```
program ::= defs
repl_input ::= stmts

stmt ::= def | expr
stmts ::= (stmt (";" stmt)*)? ";"?
alts ::= (stmt ("|" stmt)*)? "|"?

def ::= pat "=" expr
defs ::= (def (";" def)*)? ";"?

exprs ::= types ::= (expr ("," expr)*)? ","?

expr ::=
pat ::=
type ::= 
    | type ("-!" type)? "->" type
    | type "=>" type

    | expr ":" type
    | expr "||" expr
    | expr "&&" expr
    | expr ("==" | "<" | "<=" | ">" | ">=") expr
    | expr ("+" | "-") expr
    | expr ("*" | "/") expr
    | expr OTHER_INFIX expr
    | expr expr+
    | PREFIX expr
    | expr POSTFIX
    | expr "." ID

    | "{" ("|" pat ("," pat)* "->" expr)+ "}" (* function literal *)
    | "{" "|" "->" stmts "}" (* thunk *)
    | "{" "|" "}" (* empty function (uncallable) *)
    | "{" ("|" pat ("," pat)* "=>" expr)+ "}" (* implicit function literal *)
    | "{" stmts "}"
    | "[" exprs "]"
    | "(" exprs ")"
    | "(" ( "||" | "&&"
          | "==" | "<" | "<=" | ">" | ">="
          | "+" | "-"
          | "*" | "/" | "%" ) ")"
    | "{" ":" stmts "}"
    | "[" "|" alts "]"
    | "(" "|" alts ")"
    | "(" ":" types ")"

    | ID
    | "_"
    | CONST
```

See [the intro](https://broom.readthedocs.io/en/latest/introduction.html) for a slightly more detailed exposition.

