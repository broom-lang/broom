%{
open Util

open Ast
open Expr
open Stmt
open Decl

(* TODO: or-patterns *)

let parenthesized args pos =
    if Vector.length args = 1
    then Vector.get args 0
    else {v = Tuple args; pos}

%}

%token
    EFFOW "-!" ARROW "->" LARROW "<-" DARROW "=>" EQ "="
    DOT "." COLON ":" COMMA "," SEMI ";"
    HASH "#" BAR "|" ET "&" BANG "!" QMARK "?" AT "@" BACKSLASH
    LPAREN "(" RPAREN ")" LBRACKET "[" RBRACKET "]" LBRACE "{" RBRACE "}"
    EOF
%token <string> DISJUNCTION "||" CONJUNCTION "&&" COMPARISON ADDITIVE MULTIPLICATIVE
%token <Ast.Primop.t> PRIMOP
%token <string> WILD "_" ID OP
%token <string> STRING
%token <int> INT

%start program modul stmts
%type <Ast.Program.t> program
%type <Ast.Expr.t> modul
%type <Ast.Stmt.t Vector.t> stmts

%%

(* # Notation *)

(* (separator item)* separator? terminator *)
tail(separator, item, terminator) :
    | separator item tail(separator, item, terminator) { $2 :: $3 }
    | separator? terminator { [] }

(* (item (separator item)* )? separator? terminator *)
trail(separator, item, terminator) :
    | item tail(separator, item, terminator) { Vector.of_list ($1 :: $2) }
    | terminator { Vector.empty }

(* init (item (separator item)* )? separator? terminator *)
trailer(init, separator, item, terminator) : init trail(separator, item, terminator) { $2 }

(* # Compilation Units *)

(* (def ";")* expr ";"? EOF *)
program : parse_program {
    let (defs, body) = $1 in
    {Ast.Program.span = $loc; defs = Vector.of_list defs; body}
}

parse_program :
    | def ";" parse_program {
        let (defs, body) = $3 in
        ($1 :: defs, body)
    }
    | expr ";"? EOF { ([], $1) }

modul : expr EOF { $1 }

stmts : trail(";", stmt, EOF) { $1 }

(* # Terms *)

(* ## Expressions *)

expr : annotated { $1 }

annotated :
    | app ":" typ { {v = Ann ($1, $3); pos = $loc} } (* NOTE: ~ right-associative *)
    | app { $1 }

app :
    | PRIMOP select+ { {v = PrimApp ($1, Vector.of_list $2); pos = $loc} }
    | select select+ { {v = App (Vector.of_list ($1 :: $2)); pos = $loc} }
    | select { $1 }

select :
    | select "." ID { {v = Select ($1, Name.of_string $3); pos = $loc} }
    | select "." INT { {v = Focus ($1, $3); pos = $loc} }
    | aexpr { $1 }

aexpr : aexpr_without_pos { {v = $1; pos = $sloc} }

aexpr_without_pos :
    | "[" "|" "]" { Fn Vector.empty }
    | "[" clauses "]" { $2 }
    | "[" stmts "]" {
        let body = App (Vector.of_array_unsafe
            [| {v = Var (Name.of_string "do"); pos = $loc}
            ; {v = Record $2; pos = $loc} |]) in
        Fn (Vector.singleton
            { params = {v = Tuple Vector.empty; pos = $loc($1)}
            ; body = {v = body; pos = $loc} })
    }
    | fn_typ { $1 }

    | trailer("{", ";", stmt, "}") { Record $1 }
    | "{" ":" trail(";", decl, "}") { RecordT $3 }

    | tuple { Tuple $1 }
    | "(" ":" trail(",", typ, ")") { TupleT $3 }

    | "(" "#" trail(";", decl, ")") { VariantT $3 }

    | "(" "|" trail(";", decl, ")") { RowT $3 }

    | "(" expr ")" { $2.v }
    | "(" "||" ")" { Var (Name.of_string $2) }
    | "(" "&&" ")" { Var (Name.of_string $2) }
    | "(" COMPARISON ")" { Var (Name.of_string $2) }
    | "(" ADDITIVE ")" { Var (Name.of_string $2) }
    | "(" MULTIPLICATIVE ")" { Var (Name.of_string $2) }

    | ID { Var (Name.of_string $1) }
    | "_" { Wild (Name.of_string $1) }
    | INT { Const (Int $1) } | STRING { Const (String $1) } 

clauses :
    | explicit_clause+ { Fn (Vector.of_list $1) }
    | implicit_clause+ { ImpliFn (Vector.of_list $1) }

explicit_clause : "|" select+ "->" expr {
        {params = parenthesized (Vector.of_list $2) $loc($3); body = $4}
    }

implicit_clause : "|" select+ "=>" expr {
        {params = parenthesized (Vector.of_list $2) $loc($3); body = $4}
    }

tuple :
    | "(" ","? ")" { Vector.empty }
    | "(" expr "," ")" { Vector.singleton $2 }
    | "(" expr "," expr tail(",", expr, ")") { Vector.of_list ($2 :: $4 :: $5) }

fn_typ :
    | "[" pat "-!" typ "->" typ "]" {
        PiT {domain = $2; eff = Some $4; codomain = $6}
    }
    | "[" pat "->" typ "]" {
        PiT {domain = $2; eff = None; codomain = $4}
    }
    | "[" pat "=>" typ "]" {
        ImpliT {domain = $2; codomain = $4}
    }

(* ## Patterns *)

pat : expr { $1 }

(* ## Definitions *)

def : pat "=" expr { ($loc, $1, $3) }

(* ## Statements *)

stmt :
    | def {
        let (span, pat, expr) = $1 in
        Def (span, pat, expr)
    }
    | expr { Expr $1 }

(* # Types *)

typ : expr { $1 }

(* ## Declarations *)

decl :
    | def {
        let (span, pat, expr) = $1 in
        Def (span, pat, expr)
    }
    | app ":" typ { Decl ($loc, $1, $3) }
    | app { Type $1 }

