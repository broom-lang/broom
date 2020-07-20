# Broom Rewrite in OCaml

## (Abstract) Syntax

```
expr ::= type ::= "pi" apat+ "->" type
    | type "->" type
    | "pi" apat+ "=>" type
    | type "=>" type
    | expr ":" type
    | expr expr+
    | expr "." ID
    | "let" reclet
    | "begin" beginet
    | "module" ("extends" def ";")? (def ";")* "end"
    | "interface" ("extends" ID "=" type ";")? (decl ";")* "end"
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

reclet : (def ";")+ "begin" beginet

beginet : stmt* ("rec" reclet | "end")

row_expr ::= row_expr "with" field ("," field)*
    | row_expr "where" field ("," field)*
    | row_expr "without" ID ("," ID)*
    | "..." expr
    | (* empty *)

field ::= ID ("=" expr)?

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

decl ::= ID "=" type
    | "type" ID apat* "=" type

def ::= pat "=" expr
    | "fun" ID apat* "=" expr

stmt ::= def ";"
    | "do" expr ";"
```

