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
    FUN "fun" PI "pi" VAL "val" TYPE "type" TYPEOF "typeof" BEGIN "begin" DO "do" END "end"
    WITH "with" WHERE "where" WITHOUT "without"
    ARROW "->" DARROW "=>" DOT "." COLON ":" EQ "=" COMMA "," SEMI ";" BAR "|"
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

%type <Ast.Term.expr with_pos> expr
%type <Ast.Term.clause> clause
%type <Ast.Term.expr> row_expr

%type <Ast.Pattern.t with_pos> pat apat

%%

program : stmts EOF { $1 }

(* # Types *)

typ : typ_without_pos { {v = $1; pos = $sloc} }

typ_without_pos
    : domain "=>" typ { Pi ($1, Pure, $3) }
    | domain "->" typ { Pi ($1, Impure, $3) }
    | "typeof" ann_expr { Singleton $2 }
    | ann_expr { path $1.v }

domain
    : "pi" apat* { Vector.of_list $2 }
    | unann_expr { Vector.singleton {v = Pattern.Ann ({v = Pattern.Ignore; pos = $sloc}, {v = path $1.v; pos = $sloc}); pos = $sloc} }

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
    | "{" row_expr "}" { $2 }
    | "{" superless_row "}" { $2 }
    | "[" clause* "]" { Fn (Vector.of_list $2) }
    | "[" expr "]" { Fn (Vector.singleton {pats = Vector.of_list []; body = $2}) }
    | "begin" begin_def* expr "end" {
        match Vector1.of_list $2 with
        | Some defs -> Begin (defs, $3)
        | None -> $3.v
    } 
    | "do" stmts "end" { Do $2 }
    | "{" "|" decls=separated_list(";", decl) "|" "}" { proxy (Sig (Vector.of_list decls)) }
    | "(" typ ")" { proxy $2.v }
    | "type" { proxy Type }
    | atom { $1 }

row_expr :
    | with_row { $1 }
    | where_row { $1 }
    | without_row { $1 }
    | { EmptyRecord }

with_row :
    | row_or_expr "with" field { With ($1, fst $3, snd $3) }
    | with_row "," field { With ({v = $1; pos = $loc($1)}, fst $3, snd $3) }

where_row :
    | row_or_expr "where" field { Where ($1, fst $3, snd $3) }
    | where_row "," field { Where ({v = $1; pos = $loc($1)}, fst $3, snd $3) }

without_row :
    | row_or_expr "without" ID { Without ($1, Name.of_string $3) }
    | without_row "," ID { Without ({v = $1; pos = $loc($1)}, Name.of_string $3) }

row_or_expr :
    | expr { $1 }
    | row_expr { {v = $1; pos = $sloc} }

superless_row :
    | superless_row "," field { With ({v = $1; pos = $loc($1)}, fst $3, snd $3) }
    | field { With ({v = EmptyRecord; pos = $loc($1)}, fst $1, snd $1) }

field
    : ID "=" expr { (Name.of_string $1, $3) }
    | ID { failwith "TODO" }

clause : "|" apat+ "->" expr { failwith "TODO" }

begin_def : def ";" { $1 }

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
    : "val" name=ID ":" typ=typ { {name = Name.of_string name; typ} }
    | "type" name=ID "=" typ=typ {
        {name = Name.of_string name; typ = {v = Singleton {v = proxy typ.v; pos = $loc(typ)}; pos = $sloc}}
    }
    | "type" name=ID { {name = Name.of_string name; typ = {v = Type; pos = $loc(name)}} }

(* # Definitions and Statements *)

stmts : separated_list(";", stmt) { Vector.of_list $1 }

stmt
    : def { Def $1 }
    | expr { Expr $1 }

def : "val" pat "=" expr { ($sloc, $2, $4) }

(* # Patterns *)

pat :
    | apat ":" typ { {v = Pattern.Ann ($1, $3); pos = $sloc} }
    | apat { $1 }

apat :
    | "(" pat ")" { $2 }
    | ID { {v = Pattern.Binder (Name.of_string $1); pos = $sloc} }
    | CONST { failwith "TODO" }

