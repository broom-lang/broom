%{
open Ast.Type
open Ast.Term.Expr
open Ast.Term.Stmt
open Util

(* TODO: or-patterns *)

let path = function
    | Proxy typ -> typ
    | expr -> Path expr

let proxy = function
    | Path expr -> expr
    | typ -> Proxy typ

let parenthesized args pos =
    if Vector.length args = 1
    then Vector.get args 0
    else {v = Tuple args; pos}

%}

%token
    EFFOW "-!" ARROW "->" LARROW "<-" DARROW "=>" EQ "="
    DOT "." COLON ":" COMMA "," SEMI ";"
    HASH "#" BAR "|" BANG "!" QMARK "?" AT "@" BACKSLASH
    LPAREN "(" RPAREN ")" LBRACKET "[" RBRACKET "]" LBRACE "{" RBRACE "}"
    EOF
%token <string> DISJUNCTION "||" CONJUNCTION "&&" COMPARISON ADDITIVE MULTIPLICATIVE
%token <Primop.t> PRIMOP
%token <Branchop.t> BRANCHOP
%token <string> WILD "_" ID OP
%token <string> STRING
%token <int> INT

%start program modul stmts
%type <Ast.Program.t> program
%type <Ast.Term.Expr.t with_pos> modul
%type <Ast.Term.Stmt.t Vector.t> stmts

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
    | disjunction ":" typ { {v = Ann ($1, $3); pos = $loc} } (* NOTE: ~ right-associative *)
    | disjunction { $1 }

disjunction :
    | disjunction "||" conjunction {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | conjunction { $1 }

conjunction :
    | conjunction "&&" comparison {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | comparison { $1 }

comparison :
    | additive COMPARISON additive { (* NOTE: nonassociative *)
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | additive { $1 }

additive :
    | additive ADDITIVE multiplicative {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | multiplicative { $1 }

multiplicative :
    | multiplicative MULTIPLICATIVE app {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | app { $1 }

app :
    | PRIMOP args {
        let op = $1 in
        match $2 with
        | Left _ -> failwith "primop missing explicit args"
        | Right eargs -> {v = PrimApp (op, Vector.empty, eargs); pos = $loc}
        | Both (iargs, eargs) -> {v = PrimApp (op, iargs, eargs); pos = $loc}
    }
    | BRANCHOP args {
        let op = $1 in
        match $2 with
        | Left _ -> failwith "branchop missing explicit args"
        | Right eargs ->
            assert (Vector.length eargs >= 2);
            let args = Vector.sub eargs 0 (Vector.length eargs - 1) in
            let clauses = match (Vector.get eargs (Vector.length args)).v with
                | Fn (Explicit, clauses) -> clauses
                | _ -> failwith "branchop missing clauses" in
            {v = PrimBranch (op, Vector.empty, args, clauses); pos = $loc}
        | Both (iargs, eargs) ->
            assert (Vector.length eargs >= 2);
            let args = Vector.sub eargs 0 (Vector.length eargs - 1) in
            let clauses = match (Vector.get eargs (Vector.length args)).v with
                | Fn (Explicit, clauses) -> clauses
                | _ -> failwith "branchop missing clauses" in
            {v = PrimBranch (op, iargs, args, clauses); pos = $loc}
    }
    | select args { match $2 with
        | Left iargs -> {v = App ($1, Implicit, parenthesized iargs $loc($2)); pos = $loc}
        | Right args ->
            let args = args |> Vector1.of_vector |> Option.get in
            {v = AppSequence (Vector1.append (Vector1.singleton $1) args); pos = $loc}
        | Both (iargs, eargs) ->
            let callee = {v = App ($1, Implicit, parenthesized iargs $loc($2)); pos = $loc} in
            {v = App (callee, Explicit, parenthesized eargs $loc($2)); pos = $loc}
    }
    | select { $1 }

args : select+ iargs? { match $2 with
        | None -> Ior.Right (Vector.of_list $1)
        | Some [] -> Left (Vector.of_list $1)
        | Some iargs -> Both (Vector.of_list $1, Vector.of_list iargs)
    }

iargs : "@" select* { $2 }

select :
    | select "." ID { {v = Select ($1, Name.of_string $3); pos = $loc} }
    | select "." INT { {v = Focus ($1, $3); pos = $loc} }
    | aexpr { $1 }

aexpr : aexpr_without_pos { {v = $1; pos = $sloc} }

aexpr_without_pos :
    | "[" "|" "]" { Fn (Explicit, Vector.empty) }
    | "[" clauses "]" { Fn (fst $2, Vector.of_list (snd $2)) }
    | "[" stmts "]" {
        let body = App ( {v = Var (Name.of_string "do"); pos = $loc}, Explicit
            , {v = Record $2; pos = $loc} ) in
        Fn (Explicit, Vector.singleton
            { params = {v = Tuple Vector.empty; pos = $loc($1)}
            ; body = {v = body; pos = $loc} })
    }
    | fn_typ { proxy $1 }

    | trailer("{", ";", stmt, "}") { Record $1 }
    | "{" ":" trail(";", decl, "}") { proxy (Record $3) }

    | tuple { Tuple $1 }
    | "(" ":" trail(",", typ, ")") { proxy (Tuple $3) }

    | "(" "#" trail(";", decl, ")") { proxy (Variant $3) }

    | "(" "|" trail(";", decl, ")") { proxy (Row $3) }

    | "(" expr ")" { $2.v }
    | "(" "||" ")" { Var (Name.of_string $2) }
    | "(" "&&" ")" { Var (Name.of_string $2) }
    | "(" COMPARISON ")" { Var (Name.of_string $2) }
    | "(" ADDITIVE ")" { Var (Name.of_string $2) }
    | "(" MULTIPLICATIVE ")" { Var (Name.of_string $2) }

    | ID { Var (Name.of_string $1) }
    | "_" { Wild (Name.of_string $1) }
    | INT { Const (Int $1) }
    | STRING { Const (String $1) }

clauses :
    | explicit_clause+ { (Explicit, $1) }
    | implicit_clause+ { (Implicit, $1) }

explicit_clause : "|" disjunction tail(",", disjunction, "->") expr {
        {params = parenthesized (Vector.of_list ($2 :: $3)) $loc($3); body = $4}
    }

implicit_clause : "|" disjunction tail(",", disjunction, "=>") expr {
        {params = parenthesized (Vector.of_list ($2 :: $3)) $loc($3); body = $4}
    }

tuple :
    | "(" ","? ")" { Vector.empty }
    | "(" expr "," ")" { Vector.singleton $2 }
    | "(" expr "," expr tail(",", expr, ")") { Vector.of_list ($2 :: $4 :: $5) }

fn_typ :
    | "[" pat "-!" typ "->" typ "]" {
        Pi {domain = $2; eff = Some $4; codomain = $6}
    }
    | "[" pat "->" typ "]" {
        Pi {domain = $2; eff = None; codomain = $4}
    }
    | "[" pat "=>" annotated "]" {
        Impli {domain = $2; codomain = {$4 with v = path $4.v}}
    }

(* ## Patterns *)

pat : expr { $1 }

(* ## Definitions *)

def : pat "=" expr { ($loc, $1, $3) }

(* ## Statements *)

stmt :
    | def { Def $1 }
    | expr { Expr $1 }

(* # Types *)

typ : expr { {v = path $1.v; pos = $1.pos} }

(* ## Declarations *)

decl :
    | def { Def $1 }
    | disjunction ":" typ { Decl ($loc, $1, $3) }
    | disjunction { Type {v = path $1.v; pos = $1.pos} }

