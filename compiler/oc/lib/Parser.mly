%{
open Ast
open Ast.Term
open Ast.Type
open Util
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
%type <Ast.Term.expr> typ_nestable_mixin
%type <Ast.Type.t> typ_without_pos typ_nestable_mixin_without_pos

%type <Name.t Ast.Type.decl> decl

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
    | ann_expr(typ_nestable_mixin) { Path $1.v }

domain
    : "pi" apat* { Vector.of_list $2 }
    | unann_expr(typ_nestable_mixin) { Vector.singleton {v = Pattern.Ignore; pos = $sloc} }

typ_nestable_mixin : typ_nestable_mixin_without_pos { Proxy {v = $1; pos = $sloc} }

typ_nestable_mixin_without_pos (* Non-infix types that are not valid as exprs *)
    : "{" "|" decls=separated_list(";", decl) "|" "}" { Sig (Vector.of_list decls) }
    | "typeof" expr=expr_nestable(expr_nestable_mixin) { Singleton expr }
    | "(" typ ")" { $2.v }
    | "type" { Type }

(* ## Declarations *)

decl
    : "val" name=ID ":" typ=typ { {name = Name.of_string name; typ} }
    | "type" name=ID "=" typ=typ {
        {name = Name.of_string name; typ = {v = Singleton {v = Proxy typ; pos = $loc(typ)}; pos = $sloc}}
    }
    | "type" name=ID { {name = Name.of_string name; typ = {v = Type; pos = $loc(name)}} }

(* # Expressions *)

expr :
    (*| "type" typ { {$2 with v = Proxy $2} }*)
    | ann_expr(expr_nestable_mixin) { $1 }

ann_expr(nestable_mixin)
    : expr=unann_expr(nestable_mixin) ":" ann=typ { {v = Seal (expr, ann); pos = $sloc} }
    | unann_expr(nestable_mixin) { $1 }

unann_expr(nestable_mixin) : app(nestable_mixin) { $1 }

app(nestable_mixin)
    : app(nestable_mixin) select(nestable_mixin) { {v = App ($1, $2); pos = $sloc} }
    | select(nestable_mixin) { $1 }

select(nestable_mixin)
    : record=select(nestable_mixin) "." label=ID { {v = Select (record, Name.of_string label); pos = $sloc} }
    | expr_nestable(nestable_mixin) { $1 }

expr_nestable(nestable_mixin) : expr_nestable_without_pos(nestable_mixin) { {v = $1; pos = $sloc} }

expr_nestable_without_pos(nestable_mixin) :
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
    | nestable_mixin { $1 }
    | atom { $1 }

expr_nestable_mixin (* Non-infix exprs that are not valid as types *)
    : "(" expr ")" { $2.v }

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
            | "__int" -> Proxy {v = Type.Prim Prim.Int; pos = $sloc}
            | "__bool" -> Proxy {v = Type.Prim Prim.Bool; pos = $sloc}
            | _ -> failwith ("nonexistent intrinsic " ^ $1)
        else Use (Name.of_string $1)
    }
    | CONST { Const (Const.Int $1) }

(* # Definitions and Statements *)

stmts : separated_list(";", stmt) { Vector.of_list $1 }

stmt
    : def { Def $1 }
    | expr { Expr $1 }

def :
    | "val" pat "=" expr { ($sloc, $2, $4) }
    | "type" ID "=" typ {
        ( $sloc, {v = Pattern.Binder (Name.of_string $2); pos = $loc($2)}
        , {v = Proxy $4; pos = $loc($4)} )
    }

(* # Patterns *)

pat :
    | apat ":" typ { {v = Pattern.Ann ($1, $3); pos = $sloc} }
    | apat { $1 }

apat :
    | "(" pat ")" { $2 }
    | ID { {v = Pattern.Binder (Name.of_string $1); pos = $sloc} }
    | CONST { failwith "TODO" }

