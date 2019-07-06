structure Tokens = Tokens

type arg = Pos.t
type pos = Pos.t
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

val pos = ref NONE
fun ensurePos startPos = if isSome (!pos) then () else pos := SOME startPos
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

fun tok0 startPos tok cs =
    let val _ = ensurePos startPos
        val startPos = getPos ()
        val _ = advance startPos cs
        val endPos = getPos ()
    in tok (startPos, endPos)
    end

fun tok1 startPos tok cs v =
    let val _ = ensurePos startPos
        val startPos = getPos ()
        val _ = advance startPos cs
        val endPos = getPos ()
    in tok (v, startPos, endPos)
    end

(* FIXME: If file is empty, `eof` will raise Option. *)
fun eof _ = Tokens.EOF(getPos (), getPos ())
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

\n       => (advance startPos yytext; continue());
{ws}+    => (advance startPos yytext; continue());

"="      => (tok0 startPos Tokens.EQ yytext);
"=>"     => (tok0 startPos Tokens.DARROW yytext);
":"      => (tok0 startPos Tokens.COLON yytext);
"->"     => (tok0 startPos Tokens.ARROW yytext);
".."     => (tok0 startPos Tokens.DDOT yytext);
"&"      => (tok0 startPos Tokens.AMP yytext);
"."      => (tok0 startPos Tokens.DOT yytext);
","      => (tok0 startPos Tokens.COMMA yytext);

"("      => (tok0 startPos Tokens.LPAREN yytext);
")"      => (tok0 startPos Tokens.RPAREN yytext);
"{"      => (tok0 startPos Tokens.LBRACE yytext);
"}"      => (tok0 startPos Tokens.RBRACE yytext);

"val"    => (tok0 startPos Tokens.VAL yytext);
"type"   => (tok0 startPos Tokens.TYPE yytext);
"do"     => (tok0 startPos Tokens.DO yytext);
"fn"     => (tok0 startPos Tokens.FN yytext);
"let"    => (tok0 startPos Tokens.LET yytext);
"in"     => (tok0 startPos Tokens.IN yytext);
"module" => (tok0 startPos Tokens.MODULE yytext);
"interface" => (tok0 startPos Tokens.INTERFACE yytext);
"fun"    => (tok0 startPos Tokens.FUN yytext);
"end"    => (tok0 startPos Tokens.END yytext);
"if"     => (tok0 startPos Tokens.IF yytext);
"then"   => (tok0 startPos Tokens.THEN yytext);
"else"   => (tok0 startPos Tokens.ELSE yytext);
"True"   => (tok1 startPos Tokens.BOOL yytext true);
"False"  => (tok1 startPos Tokens.BOOL yytext false);
({alpha}|_)+ => (tok1 startPos Tokens.ID yytext yytext);

{digit}+ => (tok1 startPos Tokens.INT yytext (valOf (Int.fromString yytext)));

