# 𓎝 Broom

A programming language with first-class modules and algebraic effects.  Still
very much a work in progress (i.e. not yet usable).

## Characterization and Planned Features

* Functional-first
* Strict evaluation (call by value)
* Strong static typing
    - Parametric, higher-rank and impredicative polymorphism
    - Type inference (but no let-generalization)
    - Modular implicits
    - Generalized Algebraic DataTypes
* ML-style module system
    - Also supports recursive and first-class modules
* Algebraic effects
* The modules and effects are based on row types

## (Abstract) Syntax

```
program ::= defs
repl_input ::= stmts

stmt ::= def | expr
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
    | "{" ":" stmts ")"
    | "[" "|" alts "]"
    | "(" "|" alts ")"
    | "(" ":" types ")"

    | ID
    | "_"
    | CONST
```

See [the intro](https://broom.readthedocs.io/en/latest/introduction.html) for a slightly more detailed exposition.

