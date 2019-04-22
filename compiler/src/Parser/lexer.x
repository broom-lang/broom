structure Tokens = Tokens

type arg = Pos.t
type pos = Pos.t
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

val pos = ref NONE
fun getPos () = valOf (!pos)
fun advanceOne startPos c =
    pos := SOME (case !pos
                 of SOME prev => Pos.next prev c
                  | NONE => startPos)

fun advance startPos cs =
    let fun loop i =
            if i < String.size cs
            then ( advanceOne startPos (String.sub (cs, i))
                 ; loop (i + 1) )
            else ()
    in loop 0
    end
fun eof _ = Tokens.EOF(getPos (), getPos ())
fun error (e, l, r) = TextIO.output (TextIO.stdOut, String.concat[
        "line ", Pos.toString l, "-", Pos.toString r, ": ", e, "\n"
      ])

(* FIXME: Should take the pos before `advance` as the left pos. *)

%%

%header (functor BroomLexFun(structure Tokens: Broom_TOKENS));
%arg (startPos);

alpha = [A-Za-z];
digit = [0-9];
ws = [\ \t];

%%

\n       => (advance startPos yytext; continue());
{ws}+    => (advance startPos yytext; continue());

"="      => (advance startPos yytext; Tokens.EQ(getPos (), getPos ()));
"=>"     => (advance startPos yytext; Tokens.DARROW(getPos (), getPos ()));
":"      => (advance startPos yytext; Tokens.COLON(getPos (), getPos ()));
"->"     => (advance startPos yytext; Tokens.ARROW(getPos (), getPos ()));
"."      => (advance startPos yytext; Tokens.DOT(getPos (), getPos ()));

"("      => (advance startPos yytext; Tokens.LPAREN (getPos (), getPos ()));
")"      => (advance startPos yytext; Tokens.RPAREN (getPos (), getPos ()));

"val"    => (advance startPos yytext; Tokens.VAL (getPos (), getPos ()));
"fn"     => (advance startPos yytext; Tokens.FN (getPos (), getPos ()));
"forall" => (advance startPos yytext; Tokens.FORALL (getPos (), getPos ()));
"let"    => (advance startPos yytext; Tokens.LET (getPos (), getPos ()));
"in"     => (advance startPos yytext; Tokens.IN (getPos (), getPos ()));
"end"    => (advance startPos yytext; Tokens.END (getPos (), getPos ()));
{alpha}+ => (advance startPos yytext; Tokens.ID (yytext, getPos (), getPos ()));

{digit}+ => (advance startPos yytext; Tokens.INT (valOf (Int.fromString yytext), getPos (), getPos ()));

