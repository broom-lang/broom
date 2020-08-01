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
    (*FUN "fun" PI "pi" VAL "val" TYPE "type" TYPEOF "typeof" LET "let" BEGIN "begin" DO "do" END "end"
    WITH "with" WHERE "where" WITHOUT "without" MODULE "module" INTERFACE "interface" EXTENDS "extends" *)
    ARROW "->" DARROW "=>" DOT "." COLON ":" EQ "=" COMMA "," SEMI ";" BAR "|" (* ELLIPSIS "..." *)
    BANG "!" QMARK "?" HASH "#" AT "@"
    QUOTE "'" BQUOTE "`"
    LPAREN "(" RPAREN ")"
    LBRACKET "[" RBRACKET "]"
    LBRACE "{" RBRACE "}"
    EOF
%token <string> OP1 OP2 OP3 OP4 OP5 OP6 PRIMOP ID WILD (* FIXME: actually design infix operators *)
%token <int> CONST

%start <Ast.Term.stmt Vector.t> program

(*
%type <Ast.Type.t with_pos> typ
%type <Ast.Pattern.t with_pos Vector.t> domain
%type <Ast.Type.t> typ_without_pos

%type <Name.t Ast.Type.decl> decl

%type <Ast.Term.expr with_pos> expr row_expr
%type <Ast.Term.expr> block
%type <Ast.Term.clause> clause

%type <Ast.Pattern.t with_pos> pat apat
*)

%%

program : separated_list(";", def) EOF { failwith "TODO" }

(* # Definitions & Statements *)

def : expr "=" expr { failwith "TODO" }

stmt :
    | def { failwith "TODO" }
    | expr { failwith "TODO" }

(* # Expressions *)

expr : typ { failwith "TODO" }

ann_expr :
    | binapp ":" typ { failwith "TODO" } (* NOTE: ~ right-associative *)
    | binapp { failwith "TODO" }

binapp :
    | binapp OP1 binapp2 { failwith "TODO" }
    | binapp2 { failwith "TODO" }

binapp2 :
    | binapp2 OP2 binapp3 { failwith "TODO" }
    | binapp3 { failwith "TODO" }

binapp3 :
    | binapp4 OP3 binapp4 { failwith "TODO" } (* NOTE: nonassociative *)
    | binapp4 { failwith "TODO" }

binapp4 :
    | binapp4 OP4 binapp5 { failwith "TODO" }
    | binapp5 { failwith "TODO" }

binapp5 :
    | binapp5 OP5 binapp6 { failwith "TODO" }
    | binapp6 { failwith "TODO" }

binapp6 :
    | binapp6 OP6 app { failwith "TODO" }
    | app { failwith "TODO" }

app :
    | prefix_app params? { failwith "TODO" }
    | PRIMOP params? { failwith "TODO" }

prefix_app :
    | "'" select { failwith "TODO" }
    | "`" select { failwith "TODO" }
    | "?" select { failwith "TODO" }
    | "#" select { failwith "TODO" }
    | select { failwith "TODO" }

select :
    | select "." nestable { failwith "TODO" }
    | nestable { failwith "TODO" }

nestable :
    | "{" separated_list(";", stmt) "}" { failwith "TODO" }
    | "[" clause* "]" { failwith "TODO" }
    | "[" expr "]" { failwith "TODO" }
    | "(" separated_list(",", expr) ")" { failwith "TODO" } (* unit, expr, tuple/`values` *)
    | "(" OP1 ")" { failwith "TODO" }
    | "(" OP2 ")" { failwith "TODO" }
    | "(" OP3 ")" { failwith "TODO" }
    | "(" OP4 ")" { failwith "TODO" }
    | "(" OP5 ")" { failwith "TODO" }
    | "(" OP6 ")" { failwith "TODO" }
    | ID { failwith "TODO" }
    | WILD { failwith "TODO" }
    | CONST { failwith "TODO" }

clause : "|" params? "->" expr { failwith "TODO" }

params : prefix_app* "@" prefix_app* { failwith "TODO" }

(* # Types *)

typ : binapp "->" typ "!" typ { failwith "TODO" }
    | binapp "=>" typ { failwith "TODO" }
    | ann_expr { failwith "TODO" }

(*
program : separated_list(";", stmt) EOF { Vector.of_list $1 }

(* # Types *)

typ : typ_without_pos { {v = $1; pos = $sloc} }

typ_without_pos :
    | domain "->" row "!" typ { Pi ($1, Impure, $5) } (* FIXME: use effect row *)
    | domain "=>" typ { Pi ($1, Pure, $3) }
    | "typeof" ann_expr { Typeof $2 }
    | ann_expr { path $1.v }

domain
    : "pi" apat* { Vector.of_list $2 }
    | unann_expr { Vector.singleton {v = Pattern.Ann ({v = Pattern.Ignore; pos = $sloc}, {v = path $1.v; pos = $sloc}); pos = $sloc} }

nestable_typ :
    | "{" "|" row "|" "}" { Record $3 }
    | "(" "|" row "|" ")" { $3.v }
    | "interface" super_typ interface_tail { Interface (Some $2, Vector.of_list $3) }
    | "interface" decl interface_tail { Interface (None, Vector.of_list ($2 :: $3)) }
    | "interface" "end" { Interface (None, Vector.of_list []) }
    | "(" typ ")" { $2.v }
    | "type" { Type }

super_typ : "extends" ID ":" typ { (Name.of_string $2, $4) }

interface_tail :
    | ";" decl interface_tail { $2 :: $3 }
    | ";"? "end" { [] }

row :
    | with_row { {v = $1; pos = $loc} }
    | where_row { {v = $1; pos = $loc} }
    | without_row { {v = $1; pos = $loc} }
    | superless_row { {v = $1; pos = $loc} }
    | "..." typ { $2 }
    | { {v = EmptyRow; pos = $loc} }

with_row :
    | row "with" typ_field { With ($1, $3.name, $3.typ) }
    | with_row "," typ_field { With ({v = $1; pos = $loc($1)}, $3.name, $3.typ) }

where_row :
    | row "where" typ_field { Where ($1, $3.name, $3.typ) }
    | where_row "," typ_field { Where ({v = $1; pos = $loc($1)}, $3.name, $3.typ) }

without_row :
    | row "without" ID { Without ($1, Name.of_string $3) }
    | without_row "," ID { Without ({v = $1; pos = $loc($1)}, Name.of_string $3) }

superless_row :
    | superless_row "," typ_field { With ({v = $1; pos = $loc($1)}, $3.name, $3.typ) }
    | typ_field { With ({v = EmptyRow; pos = $loc}, $1.name, $1.typ) }

typ_field :
    | decl { $1 }
    | ID { let name = Name.of_string $1 in {name; typ = {v = path (Use name); pos = $loc}} }

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
    | "module" super module_tail "end" { Module (Some $2, Vector.of_list $3) }
    | "module" def module_tail "end" { Module (None, Vector.of_list $3) }
    | "module" "end" { Module (None, Vector.of_list []) }
    | block { $1 }
    | nestable_typ { proxy $1 }
    | atom { $1 }

super : "extends" def { let (_, pat, expr) = $2 in (pat, expr) }

module_tail :
    | ";" def module_tail { $2 :: $3 }
    | ";"? "end" { [] }

row_expr :
    | with_row_expr { {v = $1; pos = $loc} }
    | where_row_expr { {v = $1; pos = $loc} }
    | without_row_expr { {v = $1; pos = $loc} }
    | superless_row_expr { {v = $1; pos = $loc} }
    | "..." expr { $2 }
    | { {v = EmptyRecord; pos = $loc} }

with_row_expr :
    | row_expr "with" field { Term.With ($1, fst $3, snd $3) }
    | with_row_expr "," field { Term.With ({v = $1; pos = $loc($1)}, fst $3, snd $3) }

where_row_expr :
    | row_expr "where" field { Term.Where ($1, fst $3, snd $3) }
    | where_row_expr "," field { Term.Where ({v = $1; pos = $loc($1)}, fst $3, snd $3) }

without_row_expr :
    | row_expr "without" ID { Term.Without ($1, Name.of_string $3) }
    | without_row_expr "," ID { Term.Without ({v = $1; pos = $loc($1)}, Name.of_string $3) }

superless_row_expr :
    | superless_row_expr "," field { Term.With ({v = $1; pos = $loc($1)}, fst $3, snd $3) }
    | field { Term.With ({v = EmptyRecord; pos = $loc($1)}, fst $1, snd $1) }

field
    : ID "=" expr { (Name.of_string $1, $3) }
    | ID { let name = Name.of_string $1 in (name, {v = Use name; pos = $loc}) }

block :
    | "let" def_semi+ block_tail { Let (Vector1.of_list $2 |> Option.get, $3) }
    | "begin" stmt ";" begin_tail { Begin (Vector1.of_list ($2 :: fst $4) |> Option.get, snd $4) }

begin_tail :
    | stmt ";" begin_tail { ($1 :: fst $3, snd $3) }
    | block_tail { ([], $1) }

block_tail :
    | "do" expr "end" { $2 }
    | block { {v = $1; pos = $loc} }

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

(* # Definitions and Statements *)

stmt
    : def { Def $1 }
    | "do" expr { Expr $2 }

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
*)
