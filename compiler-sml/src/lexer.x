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

%%

%header (functor BroomLexFun(structure Tokens: Broom_TOKENS));
%arg (startPos);

alpha = [A-Za-z];
digit = [0-9];
ws = [\ \t];

%%

\n       => (advance yytext; continue());
{ws}+    => (advance yytext; continue());
{digit}+ => (advance yytext; Tokens.NUM (valOf (Int.fromString yytext), !pos, !pos));

"+"      => (advance yytext; Tokens.PLUS(!pos,!pos));
"*"      => (advance yytext; Tokens.TIMES(!pos,!pos));
";"      => (advance yytext; Tokens.SEMI(!pos,!pos));
{alpha}+ => (advance yytext; if yytext="print"
                             then Tokens.PRINT(!pos,!pos)
                             else Tokens.ID(yytext,!pos,!pos));
"-"      => (advance yytext; Tokens.SUB(!pos,!pos));
"^"      => (advance yytext; Tokens.CARAT(!pos,!pos));
"/"      => (advance yytext; Tokens.DIV(!pos,!pos));
"."      => (advance yytext; error ("ignoring bad character " ^ yytext, !pos, !pos); continue());
