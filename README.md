# Broom

Effective, modular, functional programming language. WIP.

## Main Features

Currently can't run any useful programs, but this is what it will be like:

* ML dialect
    - Syntax should be more wieldy and mainstream
    - No let-generalization
* ML-style module system
    - Both 'generative' (SML) and 'applicative' (OCaml) functors
* Remove ML limitations around recursion
    - Recursive modules
* First-class modules à la 1ML
    - Also subsumes e.g. higher-ranked types
* (Modular) implicits for ad-hoc polymorphism
* Row-typed records (and modules, since they are the same)
* Row-based effect system à la Koka

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
    | type "->" type "!" type
    | type "=>" type

    | expr ":" type
    | expr "||" expr
    | expr "&&" expr
    | expr ("==" | "<" | "<=" | ">" | ">=") expr
    | expr ("+" | "-") expr
    | expr ("*" | "/" | "%") expr
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

See [the intro](docs/source/introduction.rst) for a slightly more detailed exposition.

