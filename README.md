# 𓎝 Broom

A programming language with first-class modules and algebraic effects.  Still
very much a work in progress.

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
repl_input ::= stmts*

stmt ::= def | expr
stmts ::= stmt (";" stmt)*

def ::= pat "=" expr
defs ::= def (";" def)*

expr ::=
pat ::=
type ::= 
    | (type "=>")? type ("-!" type)? "->" type

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

    | "[" ("|" apat+ "->" expr)* "]" (* function literal *)
    | "[" stmts "]" (* thunk *)
    | "{" stmts? "}"
    | "(" (expr ("," expr)*)? ")"
    | "(" ( "||" | "&&"
          | "==" | "<" | "<=" | ">" | ">="
          | "+" | "-"
          | "*" | "/" | "%" ) ")"
    | "{" "|" stmts? "|" ")"
    | "(" "|" stmts? "|" ")"

    | ID
    | "_"
    | CONST
```

<!-- See [the intro](docs/source/introduction.rst) for a slightly more detailed exposition. -->

