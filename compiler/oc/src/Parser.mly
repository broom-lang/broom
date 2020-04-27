%{ open Ast %}

%token
    IF "if" THEN "then" ELSE "else" FUN "fun" TYPE "type"
    ARROW "->" DARROW "=>" DOT "." COLON ":" SEAL ":>" EQ "=" SEMI ";"
    LPAREN "(" RPAREN ")"
    LBRACKET "[" RBRACKET "]"
    LBRACE "{" RBRACE "}"
    EOF
%token <string> ID
%token <int> CONST

%start <Ast.stmt list> stmts

%%

(* # Expressions *)

exprf(nestable)
    : "if" exprf(nestable) "then" exprf(nestable) "else" exprf(nestable) {
        {v = If ($2, $4, $6); pos = $sloc}
    }
    | appf(nestable) { $1 }

appf(nestable)
    : appf(nestable) selectf(nestable) { {v = App ($1, $2); pos = $sloc} }
    | selectf(nestable) { $1 }

selectf(nestable)
    : record=selectf(nestable) "." label=ID { {v = Select (record, Name.of_string label); pos = $sloc} }
    | nestable { $1 }

expr
    : "fun" param=param "=>" body=expr { {v = Fn (param, body); pos = $sloc} }
    | seal_expr { $1 }

seal_expr
    : expr=seal_expr ":>" ann=typ { {v = Seal (expr, ann); pos = $sloc} }
    | simple_expr { $1 }

simple_expr : exprf(expr_nestable) { $1 }

expr_nestable : expr_nestable_impl { {v = $1; pos = $sloc} }

expr_nestable_impl
    : "{" defs=separated_list(";", def) "}" { Struct defs }
    | "(" expr ")" { $2.v }
    | common_nestable { $1 }

common_nestable
    : "[" typ "]" { Proxy $2 }
    | atom { $1 }

atom
    : ID {
        if $1.[0] = '_' && $1.[1] = '_' then
            match $1 with
            | "__int" -> Proxy {v = Int; pos = $sloc}
            | "__bool" -> Proxy {v = Bool; pos = $sloc}
            | _ -> failwith ("nonexistent intrinsic " ^ $1)
        else Use (Name.of_string $1)
    }
    | CONST { Const $1 }

param
    : ID { {pat = Name.of_string $1; ann = None} }
    | "(" pat=ID ":" ann=typ ")" { {pat = Name.of_string pat; ann = Some ann} }

(* # Statements *)

stmts : separated_list(";", stmt) EOF { $1 }

stmt
    : def { Def $1 }
    | expr { Expr $1 }

def 
    : pat=ID ann=ann "=" expr=expr { ($sloc, {pat = Name.of_string pat; ann}, expr) }
    | "type" pat=ID "=" typ=typ {
        ($sloc, {pat = Name.of_string pat; ann = None}, {v = Proxy typ; pos = $loc(typ)})
    }

(* # Types *)

typ
    : domain=domain "=>" codomain=typ { {v = Pi (domain, Pure, codomain); pos = $sloc} }
    | domain=domain "->" codomain=typ { {v = Pi (domain, Impure, codomain); pos = $sloc} }
    | exprf(typ_nestable) { {v = Path $1.v; pos = $sloc} }

typ_nestable : typ_nestable_impl { {v = Proxy {v = $1; pos = $sloc}; pos = $sloc} }

typ_nestable_impl
    : "{" decls=separated_list(";", decl) "}" { Sig decls }
    | "type" { Type }
    | "(" typ ")" { $2.v }
    | common_nestable { Path $1 }

domain
    : exprf(typ_nestable) { {name = None; typ = {v = Path $1.v; pos = $sloc}} }
    | "(" name=ID ":" typ=typ ")" { {name = Some (Name.of_string name); typ} }

ann
    : ":" typ=typ { Some typ }
    | { None }

(* ## Declarations *)

decl
    : name=ID ":" typ=typ { {name = Name.of_string name; typ} }
    | "type" name=ID "=" typ=typ {
        {name = Name.of_string name; typ = {v = Singleton {v = Proxy typ; pos = $loc(typ)}; pos = $sloc}}
    }
    | "type" name=ID { {name = Name.of_string name; typ = {v = Type; pos = $loc(name)}} }

