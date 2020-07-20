%{
open Ast
open Ast.Term
open Ast.Type
open Util

let path = function
    | Proxy typ -> typ
    | expr -> Path expr

let proxy = function
    | Path expr -> expr
    | typ -> Proxy typ

%}

%token
    FUN "fun" PI "pi" VAL "val" TYPE "type" TYPEOF "typeof" LET "let" BEGIN "begin" DO "do" END "end" REC "rec"
    WITH "with" WHERE "where" WITHOUT "without" MODULE "module" INTERFACE "interface" EXTENDS "extends"
    ARROW "->" DARROW "=>" DOT "." COLON ":" EQ "=" COMMA "," SEMI ";" BAR "|" ELLIPSIS "..."
    BANG "!" QMARK "?"
    LPAREN "(" RPAREN ")"
    LBRACKET "[" RBRACKET "]"
    LBRACE "{" RBRACE "}"
    EOF
%token <string> ID
%token <int> CONST

%start <Ast.Term.stmt Vector.t> program

%type <Ast.Type.t with_pos> typ
%type <Ast.Pattern.t with_pos Vector.t> domain
%type <Ast.Type.t> typ_without_pos

%type <Name.t Ast.Type.decl> decl

%type <Ast.Term.expr with_pos> expr row_expr
%type <Ast.Term.clause> clause

%type <Ast.Pattern.t with_pos> pat apat

%%

program : stmt* EOF { Vector.of_list $1 }

(* # Types *)

typ : typ_without_pos { {v = $1; pos = $sloc} }

typ_without_pos :
    | domain "->" eff=row "!" typ { Pi ($1, Impure, $5) }
    | domain "=>" typ { Pi ($1, Pure, $3) }
    | "typeof" ann_expr { Typeof $2 }
    | ann_expr { path $1.v }

domain
    : "pi" apat* { Vector.of_list $2 }
    | unann_expr { Vector.singleton {v = Pattern.Ann ({v = Pattern.Ignore; pos = $sloc}, {v = path $1.v; pos = $sloc}); pos = $sloc} }

nestable_typ :
    | "{" "|" row "|" "}" { failwith "FIXME" }
    | "(" "|" row "|" ")" { failwith "FIXME" }
    | "interface" super_typ decl_semi* "end" { Interface ($2, Vector.of_list $3) }
    | "(" typ ")" { $2.v }
    | "type" { Type }

super_typ :
    | "extends" ID "=" typ ";" { Some (Name.of_string $2, $4) }
    | { None }

row :
    | with_row { failwith "TODO" }
    | where_row { failwith "TODO" }
    | without_row { failwith "TODO" }
    | superless_row { failwith "TODO" }
    | "..." typ { failwith "TODO" }
    | { failwith "TODO" }

with_row :
    | row "with" typ_field { failwith "TODO" }
    | with_row "," typ_field { failwith "TODO" }

where_row :
    | row "where" typ_field { failwith "TODO" }
    | where_row "," typ_field { failwith "TODO" }

without_row :
    | row "without" ID { failwith "TODO" }
    | without_row "," ID { failwith "TODO" }

superless_row :
    | superless_row "," typ_field { failwith "TODO" }
    | typ_field { failwith "TODO" }

typ_field :
    | decl { failwith "TODO" }
    | ID { failwith "TODO" }

(* # Expressions *)

expr : typ { {$1 with v = proxy $1.v} }

ann_expr
    : expr=unann_expr ":" ann=typ { {v = Ann (expr, ann); pos = $sloc} }
    | unann_expr { $1 }

unann_expr : app { $1 }

app
    : app select { {v = App ($1, $2); pos = $sloc} }
    | select { $1 }

select
    : record=select "." label=ID { {v = Select (record, Name.of_string label); pos = $sloc} }
    | nestable { $1 }

nestable : nestable_without_pos { {v = $1; pos = $sloc} }

nestable_without_pos :
    | "[" clause* "]" { Fn (Vector.of_list $2) }
    | "[" expr "]" { Fn (Vector.singleton {pats = Vector.of_list []; body = $2}) }
    | "{" row_expr "}" { $2.v }
    | "module" super def_semi* "end" { Module ($2, Vector.of_list $3) }
    | "let" reclet { $2 }
    | "begin" beginet { $2 }
    | nestable_typ { proxy $1 }
    | atom { $1 }

row_expr :
    | with_row_expr { {v = $1; pos = $loc} }
    | where_row_expr { {v = $1; pos = $loc} }
    | without_row_expr { {v = $1; pos = $loc} }
    | superless_row_expr { {v = $1; pos = $loc} }
    | "..." expr { $2 }
    | { {v = EmptyRecord; pos = $loc} }

with_row_expr :
    | row_expr "with" field { With ($1, fst $3, snd $3) }
    | with_row_expr "," field { With ({v = $1; pos = $loc($1)}, fst $3, snd $3) }

where_row_expr :
    | row_expr "where" field { Where ($1, fst $3, snd $3) }
    | where_row_expr "," field { Where ({v = $1; pos = $loc($1)}, fst $3, snd $3) }

without_row_expr :
    | row_expr "without" ID { Without ($1, Name.of_string $3) }
    | without_row_expr "," ID { Without ({v = $1; pos = $loc($1)}, Name.of_string $3) }

superless_row_expr :
    | superless_row_expr "," field { With ({v = $1; pos = $loc($1)}, fst $3, snd $3) }
    | field { With ({v = EmptyRecord; pos = $loc($1)}, fst $1, snd $1) }

field
    : ID "=" expr { (Name.of_string $1, $3) }
    | ID { let name = Name.of_string $1 in (name, {v = Use name; pos = $loc}) }

super :
    | "extends" def_semi { let (_, pat, expr) = $2 in Some (pat, expr) }
    | { None }

reclet :
    | def_semi+ "begin" beginet { match Vector1.of_list $1 with
        | Some defs -> Let (defs, {v = $3; pos = $loc($3)})
        | None -> failwith "unreachable"
    }

beginet :
    | stmt* "rec" reclet { Begin (Vector.of_list ($1 @ [Expr {v = $3; pos = $loc($3)}])) } (* OPTIMIZE *)
    | stmt* "end" { Begin (Vector.of_list $1) }

clause : "|" apat+ "->" expr { failwith "TODO" }

atom
    : ID {
        if $1.[0] = '_' && $1.[1] = '_' then
            match $1 with
            | "__int" -> proxy (Type.Prim Prim.Int)
            | "__bool" -> proxy (Type.Prim Prim.Bool)
            | _ -> failwith ("nonexistent intrinsic " ^ $1)
        else Use (Name.of_string $1)
    }
    | CONST { Const (Const.Int $1) }

(* # Declarations *)

decl
    : name=ID ":" typ=typ { {name = Name.of_string name; typ} }
    | "type" name=ID "=" typ=typ {
        {name = Name.of_string name; typ = {v = Typeof {v = proxy typ.v; pos = $loc(typ)}; pos = $sloc}}
    }
    | "type" name=ID { {name = Name.of_string name; typ = {v = Type; pos = $loc(name)}} }

decl_semi : decl ";" { $1 }

(* # Definitions and Statements *)

stmt
    : def_semi { Def $1 }
    | "do" expr ";" { Expr $2 }

def : pat "=" expr { ($sloc, $1, $3) }

def_semi : def ";" { $1 }

(* # Patterns *)

pat :
    | apat ":" typ { {v = Pattern.Ann ($1, $3); pos = $sloc} }
    | apat { $1 }

apat :
    | "(" pat ")" { $2 }
    | ID { {v = Pattern.Binder (Name.of_string $1); pos = $sloc} }
    | CONST { failwith "TODO" }

