structure Tokens = Tokens

type arg = Pos.t
type pos = Pos.t
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos = ref (Pos.default "TODO")
fun advance cs =
    let fun loop i =
            if i < String.size cs
            then ( pos := Pos.next (!pos) (String.sub (cs, i))
                 ; loop (i + 1) )
            else ()
    in  loop 0
    end
fun eof _ = Tokens.EOF(!pos, !pos)
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

\n       => (advance yytext; continue());
{ws}+    => (advance yytext; continue());

"="      => (advance yytext; Tokens.EQ(!pos, !pos));
"=>"     => (advance yytext; Tokens.DARROW(!pos, !pos));

"("      => (advance yytext; Tokens.LPAREN (!pos, !pos));
")"      => (advance yytext; Tokens.RPAREN (!pos, !pos));

"val"    => (advance yytext; Tokens.VAL (!pos, !pos));
"fn"     => (advance yytext; Tokens.FN (!pos, !pos));
{alpha}+ => (advance yytext; Tokens.ID (yytext, !pos, !pos));

{digit}+ => (advance yytext; Tokens.INT (valOf (Int.fromString yytext), !pos, !pos));
