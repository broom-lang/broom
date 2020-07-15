# Broom Rewrite in OCaml

## Syntax

```
expr ::= type ::= "pi" apat+ "->" type
    | type "->" type
    | "pi" apat+ "=>" type
    | type "=>" type
    | expr ":" type
    | expr expr+
    | expr "." ID
    | "begin" (def ";")* expr "end"
    | "do" (stmt (";" stmt)*)? "end"
    | "[" ("|" apat+ "->" expr)* "]" (* function literal *)
    | "[" expr "]" (* thunk *)
    | "{" row_expr "}"
    | "{" field ("," field)* "}" (* := "{" "with" field ("," field)* "}" *) 
    | "{" "|" row "|" ")"
    | "(" "|" row "|" ")"
    | "typeof" expr
    | "type"
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

row ::= (row "with")? ID ":" type ("," ID ":" type)*
    | row "where" ID ("." ID)* ":" type
    | row "where" "type" ID ("." ID)* apat* "=" type
    | type

decl ::= "val" ID "=" type
    | "type" ID apat* "=" type

def ::= "val" pat "=" expr
    | "fun" ID apat* "=" expr

stmt ::= def | expr
```

