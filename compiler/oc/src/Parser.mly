%{
open Ast
open Ast.Term
open Ast.Type
%}

%token
    IF "if" THEN "then" ELSE "else" FUN "fun" PI "pi" VAL "val" TYPE "type"
    ARROW "->" DARROW "=>" DOT "." COLON ":" EQ "=" SEMI ";" BAR "|"
    LPAREN "(" RPAREN ")"
    LBRACKET "[" RBRACKET "]"
    LBRACE "{" RBRACE "}"
    EOF
%token <string> ID
%token <int> CONST

%start <Ast.Term.stmt list> stmts

%type <Ast.Type.t with_pos> typ
%type <Name.t option Ast.Type.decl> domain
%type <Ast.Term.expr> typ_nestable_mixin
%type <Ast.Type.t> typ_impl typ_nestable_mixin_impl
%type <Ast.Type.t with_pos option> ann

%type <Name.t Ast.Type.decl> decl

%%

(* # Types *)

typ : typ_impl { {v = $1; pos = $sloc} }

typ_impl
    : domain=domain "=>" codomain=typ { Pi (domain, Pure, codomain) }
    | domain=domain "->" codomain=typ { Pi (domain, Impure, codomain) }
    | ann_expr(typ_nestable_mixin) { Path $1.v }

domain
    : "pi" "(" name=ID ":" typ=typ ")" { {name = Some (Name.of_string name); typ} }
    | unann_expr(typ_nestable_mixin) { {name = None; typ = {$1 with v = Path $1.v}} }

typ_nestable_mixin : typ_nestable_mixin_impl { Proxy {v = $1; pos = $sloc} }

typ_nestable_mixin_impl
    : "{" "|" decls=separated_list(";", decl) "|" "}" { Sig (Vector.of_list decls) }
    | "(" "=" expr=expr ")" { Singleton expr }
    | "(" typ ")" { $2.v }
    | "type" { Type }

ann
    : ":" typ=typ { Some typ }
    | { None }

(* ## Declarations *)

decl
    : "val" name=ID ":" typ=typ { {name = Name.of_string name; typ} }
    | "type" name=ID "=" typ=typ {
        {name = Name.of_string name; typ = {v = Singleton {v = Proxy typ; pos = $loc(typ)}; pos = $sloc}}
    }
    | "type" name=ID { {name = Name.of_string name; typ = {v = Type; pos = $loc(name)}} }

(* # Expressions *)

expr
    : "type" typ { {$2 with v = Proxy $2} }
    | ann_expr(expr_nestable_mixin) { $1 }

ann_expr(nestable_mixin)
    : expr=unann_expr(nestable_mixin) ":" ann=typ { {v = Seal (expr, ann); pos = $sloc} }
    | unann_expr(nestable_mixin) { $1 }

unann_expr(nestable_mixin)
    : "if" expr "then" expr "else" unann_expr(nestable_mixin) {
        {v = If ($2, $4, $6); pos = $sloc}
    }
    | app(nestable_mixin) { $1 }

app(nestable_mixin)
    : app(nestable_mixin) select(nestable_mixin) { {v = App ($1, $2); pos = $sloc} }
    | select(nestable_mixin) { $1 }

select(nestable_mixin)
    : record=select(nestable_mixin) "." label=ID { {v = Select (record, Name.of_string label); pos = $sloc} }
    | expr_nestable(nestable_mixin) { $1 }

expr_nestable(nestable_mixin) : expr_nestable_impl(nestable_mixin) { {v = $1; pos = $sloc} }

expr_nestable_impl(nestable_mixin)
    : "{" defs=separated_list(";", def) "}" { Struct (Vector.of_list defs) }
    | "[" expr "]" { failwith "todo" }
    | "[" clause+ "]" { failwith "todo" }
    | nestable_mixin { $1 }
    | atom { $1 }

expr_nestable_mixin
    : "(" expr ")" { $2.v }

clause : "|" param+ "->" expr { failwith "todo" }

atom
    : ID {
        if $1.[0] = '_' && $1.[1] = '_' then
            match $1 with
            | "__int" -> Proxy {v = Type.Prim Prim.Int; pos = $sloc}
            | "__bool" -> Proxy {v = Type.Prim Prim.Bool; pos = $sloc}
            | _ -> failwith ("nonexistent intrinsic " ^ $1)
        else Use (Name.of_string $1)
    }
    | CONST { Const (Const.Int $1) }

param
    : ID { {pat = Name.of_string $1; ann = None} }
    | "(" pat=ID ":" ann=typ ")" { {pat = Name.of_string pat; ann = Some ann} }

(* # Statements *)

stmts : separated_list(";", stmt) EOF { $1 }

stmt
    : val_def { Def $1 }
    | expr { Expr $1 }

def 
    : val_def { $1 }
    | "type" pat=ID "=" typ=typ {
        ($sloc, {pat = Name.of_string pat; ann = None}, {v = Proxy typ; pos = $loc(typ)})
    }

val_def : "val" pat=ID ann=ann "=" expr=expr { ($sloc, {pat = Name.of_string pat; ann}, expr) }

