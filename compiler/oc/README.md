# Broom Rewrite in OCaml

## (Abstract) Syntax

```
expr ::= type ::= ("pi" apat* | type) "->" row "!" type
    | ("pi" apat* | type) "=>" type
    | expr ":" type
    | expr expr+
    | expr "." ID
    | "let" reclet
    | "begin" beginet
    | "module" (("extends" def | def) (";" def)* ";"?)? "end"
    | "interface" (("extends" ID ":" type | decl) (";" decl)* ";"?)? "end"
    | "[" ("|" apat+ "->" expr)* "]" (* function literal *)
    | "[" expr "]" (* thunk *)
    | "{" row_expr "}"
    | "{" "|" row "|" ")"
    | "(" "|" row "|" ")"
    | "typeof" expr
    | "type"
    | ID | CONST
    | "(" expr ")"

reclet : def (";" def)* ";"? "do" expr "end"

beginet : stmt (";" stmt)* ";"? ("rec" reclet | "end") | "end"

row_expr ::= row_expr "with" field ("," field)*
    | row_expr "where" field ("," field)*
    | row_expr "without" ID ("," ID)*
    | field ("," field)* (* := "with" field ("," field)* *) 
    | "..." expr
    | (* empty *)

field ::= ID ("=" expr)?

pat ::= CTOR apat*
    | pat ":" type
    | pat "|" pat
    | pat "&" pat
    | apat

apat ::= "(" pat ")" | ID | "_" | CONST

row ::= row "with" type_field ("," type_field)*
    | row "where" type_field ("," type_field)*
    | row "without" ID ("," ID)*
    | typ_field ("," typ_field)* (* := "with" typ_field ("," typ_field)* *)
    | "..." type
    | (* empty *)

type_field ::= decl | ID

decl ::= ID "=" type
    | "type" ID apat* "=" type
    | "type" ID apat*

def ::= pat "=" expr

stmt ::= def | "do" expr
```

