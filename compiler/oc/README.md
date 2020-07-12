# Broom Rewrite in OCaml

## Syntax

```
expr ::= "[" ("|" apat+ "->" expr)* "]" (* function literal *)
    | "[" expr "]" (* thunk *)
    | expr expr+
    | "begin" (def ";")* expr "end"
    | "do" (stmt (";" stmt)*)? "end"
    | "{" row_expr "}"
    | "{" field ("," field)* "}" (* := "{" "with" field ("," field)* "}" *) 
    | expr "." ID
    | expr ":" type
    | "type" type
    | ID | CONST
    | "(" expr ")"

row_expr ::= (expr | row_expr) "with" field ("," field)*
    | (expr | row_expr) "where" field ("," field)*
    | (expr | row_expr) "without" ID ("," ID)*
    | (* empty *)

pat ::= CTOR apat*
    | pat ":" type
    | pat "|" pat
    | pat "&" pat
    | apat

apat ::= "(" pat ")" | ID | "_" | CONST

def ::= "val" pat "=" expr
    | "fun" ID apat* "=" expr
    | "type" ID apat* "=" type

stmt ::= def | expr

type ::= "pi" apat+ "->" type
    | type "->" type
    | "pi" apat+ "~>" type
    | type "~>" type
    | "pi" apat+ "=>" type
    | type "=>" type
    | "{" "|" row "|" ")"
    | "(" "|" row "|" ")"
    | expr
    | "typeof" expr
    | "type"
    | "(" type ")"

row ::= (row "with")? ID ":" type ("," ID ":" type)*
    | row "where" ID ("." ID)* ":" type
    | row "where" "type" ID ("." ID)* apat* "=" type
    | type

decl ::= "val" ID "=" type
    | "type" ID apat* "=" type
```

