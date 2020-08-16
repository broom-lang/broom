# Broom Rewrite in OCaml

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

