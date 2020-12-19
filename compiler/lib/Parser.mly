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

let parenthesized' args =
    if Vector.length args = 1
    then (Vector.get args 0).v
    else Tuple args

%}

%token
    EFFOW "-!" ARROW "->" LARROW "<-" DARROW "=>" EQ "="
    DOT "." COLON ":" COMMA "," SEMI ";"
    BAR "|" BANG "!" QMARK "?" AT "@" BACKSLASH
    LPAREN "(" RPAREN ")" LBRACKET "[" RBRACKET "]" LBRACE "{" RBRACE "}"
    EOF
%token <string> DISJUNCTION "||" CONJUNCTION "&&" COMPARISON ADDITIVE MULTIPLICATIVE
%token <Primop.t> PRIMOP
%token <Branchop.t> BRANCHOP
%token <string> WILD "_" ID OP
%token <string> STRING
%token <int> INT

%start defs stmts
%type <Ast.Term.Stmt.def Vector.t> defs
%type <Ast.Term.Stmt.t Vector.t> stmts

%%

tail(separator, item, terminator) :
    | separator item tail(separator, item, terminator) { $2 :: $3 }
    | separator? terminator { [] }

trail(separator, item, terminator) :
    | item tail(separator, item, terminator) { Vector.of_list ($1 :: $2) }
    | terminator { Vector.empty }

trailer(init, separator, item, terminator) : init trail(separator, item, terminator) { $2 }

(* # Entry Points *)

defs : trail(";", def, EOF) { $1 }

stmts : trail(";", stmt, EOF) { $1 }

(* # Definitions & Statements *)

def : expr "=" expr { ($loc, $1, $3) }

stmt :
    | def { Def $1 }
    | expr { Expr $1 }

(* # Expressions *)

expr : typ { {$1 with v = proxy $1.v} }

ann_expr :
    | binapp ":" typ { {v = Ann ($1, $3); pos = $loc} } (* NOTE: ~ right-associative *)
    | binapp { $1 }

binapp :
    | binapp "||" binapp2 {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | binapp2 { $1 }

binapp2 :
    | binapp2 "&&" binapp3 {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | binapp3 { $1 }

binapp3 :
    | binapp4 COMPARISON binapp4 { (* NOTE: nonassociative *)
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | binapp4 { $1 }

binapp4 :
    | binapp4 ADDITIVE binapp5 {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | binapp5 { $1 }

binapp5 :
    | binapp5 MULTIPLICATIVE app {
        let operator = {v = Var (Name.of_string $2); pos = $loc($2)} in
        {v = App (operator, Explicit, {v = Tuple (Vector.of_list [$1; $3]); pos = $loc}); pos = $loc}
    }
    | app { $1 }

app :
    | PRIMOP args {
        let op = $1 in
        match $2 with
        | Left iargs -> failwith "primop missing explicit args"
        | Right eargs -> {v = PrimApp (op, None, (parenthesized eargs $loc($2))); pos = $loc}
        | Both (iargs, eargs) ->
            {v = PrimApp (op, Some (parenthesized iargs $loc($2))
                , parenthesized eargs $loc($2)); pos = $loc}
    }
    | BRANCHOP args {
        let op = $1 in
        match $2 with
        | Left iargs -> failwith "branchop missing explicit args"
        | Right eargs ->
            assert (Vector.length eargs >= 2);
            let args = Vector.sub eargs 0 (Vector.length eargs - 1) in
            let clauses = match (Vector.get eargs (Vector.length args)).v with
                | Fn (Explicit, clauses) -> clauses
                | _ -> failwith "branchop missing clauses" in
            {v = PrimBranch (op, None, parenthesized args $loc($2), clauses); pos = $loc}
        | Both (iargs, eargs) ->
            assert (Vector.length eargs >= 2);
            let args = Vector.sub eargs 0 (Vector.length eargs - 1) in
            let clauses = match (Vector.get eargs (Vector.length args)).v with
                | Fn (Explicit, clauses) -> clauses
                | _ -> failwith "branchop missing clauses" in
            {v = PrimBranch (op, Some (parenthesized iargs $loc($2))
                , parenthesized args $loc($2), clauses); pos = $loc}
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

select :
    | select "." ID { {v = Select ($1, Name.of_string $3); pos = $loc} }
    | select "." INT { {v = Focus ($1, $3); pos = $loc} }
    | nestable { $1 }

nestable : nestable_without_pos { {v = $1; pos = $sloc} }

nestable_without_pos :
    | trailer("{", ";", stmt, "}") { Record $1 }
    | "{" clauses "}" { Fn (fst $2, Vector.of_list (snd $2)) }
    | "{" "|" "->" stmt tail(";", stmt, "}") {
        let body = App ( {v = Var (Name.of_string "do"); pos = $loc}, Explicit
            , {v = Record (Vector.of_list ($4 :: $5)); pos = $loc} ) in
        Fn (Explicit, Vector.singleton
            { params = {v = Tuple Vector.empty; pos = $loc($3)}
            ; body = {v = body; pos = $loc} })
    }
    | "{" "|" "}" { Fn (Explicit, Vector.empty) }
    | trailer("(", ",", expr, ")") { parenthesized' $1 }
    | "(" "||" ")" { Var (Name.of_string $2) }
    | "(" "&&" ")" { Var (Name.of_string $2) }
    | "(" COMPARISON ")" { Var (Name.of_string $2) }
    | "(" ADDITIVE ")" { Var (Name.of_string $2) }
    | "(" MULTIPLICATIVE ")" { Var (Name.of_string $2) }
    | "(" "|" stmt tail("|", stmt, ")") { proxy (Row (Vector.of_list ($3 :: $4))) }
    | "(" "|" ")" { proxy (Row Vector.empty) }
    | "{" ":" stmt tail(";", stmt, "}") { proxy (Record (Vector.of_list ($3 :: $4))) }
    | "{" ":" "}" { proxy (Record Vector.empty) }
    | "(" ":" typ tail(",", typ, ")") { proxy (Ast.Type.Tuple (Vector.of_list ($3 :: $4))) }
    | "(" ":" ")" { proxy (Ast.Type.Tuple Vector.empty) }
    | ID { Var (Name.of_string $1) }
    | "_" { Wild (Name.of_string $1) }
    | INT { Const (Int $1) }

clauses :
    | explicit_clause+ { (Explicit, $1) }
    | implicit_clause+ { (Implicit, $1) }

explicit_clause : "|" binapp tail(",", binapp, "->") expr {
        {params = parenthesized (Vector.of_list ($2 :: $3)) $loc($3); body = $4}
    }

implicit_clause : "|" binapp tail(",", binapp, "=>") expr {
        {params = parenthesized (Vector.of_list ($2 :: $3)) $loc($3); body = $4}
    }

args :
    | select+ "@" select+ { Both (Vector.of_list $1, Vector.of_list $3) }
    | select+ { Right (Vector.of_list $1) }
    | select+ "@" { Ior.Left (Vector.of_list $1) }

(* # Types *)

typ : typ_without_pos { {v = $1; pos = $sloc} }

typ_without_pos :
    | binapp "-!" binapp "->" typ {
        Pi {domain = $1; eff = Some {$3 with v = path $3.v}; codomain = $5}
    }
    | binapp "->" typ {
        Pi {domain = $1; eff = None; codomain = $3}
    }
    | binapp "=>" ann_expr {
        Impli {domain = $1; codomain = {$3 with v = path $3.v}}
    }
    | ann_expr { path $1.v }

