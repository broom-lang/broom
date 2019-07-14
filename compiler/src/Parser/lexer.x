structure Tokens = Tokens

type arg = Pos.t
type pos = Pos.t
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

type state =
    {pos: pos, prevTokenWasEnder: bool, prevTokenEnd: pos option} option
val startState: state = NONE
fun defaultState startPos =
    {pos = startPos, prevTokenWasEnder = false, prevTokenEnd = NONE}

val state = ref startState
fun ensurePos startPos =
    if isSome (!state)
    then ()
    else state := SOME (defaultState startPos)
fun getPos () = #pos (valOf (!state))
fun prevTokenWasEnder () =
    case !state
    of SOME {prevTokenWasEnder, ...} => prevTokenWasEnder
     | NONE => false
fun prevTokenEnd () = Option.mapPartial #prevTokenEnd (!state)
fun setPrev ender endPos =
    state := SOME (case !state
                   of SOME {pos, prevTokenWasEnder = _, prevTokenEnd = _} =>
                       {pos, prevTokenWasEnder = ender, prevTokenEnd = SOME endPos}
                    | NONE => raise Fail "unreachable")
fun advanceOne startPos c =
    state := SOME (case !state
                   of SOME {pos, prevTokenWasEnder, prevTokenEnd} =>
                       {pos = Pos.next pos c, prevTokenWasEnder, prevTokenEnd}
                    | NONE => defaultState startPos)
fun advance startPos cs =
    let fun loop i =
            if i < String.size cs
            then ( advanceOne startPos (String.sub (cs, i))
                 ; loop (i + 1) )
            else ()
    in loop 0
    end
fun reset () = state := startState

fun tok0 startPos tok ender cs =
    let val _ = ensurePos startPos
        val startPos = getPos ()
        val _ = advance startPos cs
        val endPos = getPos ()
        val _ = setPrev ender endPos
    in tok (startPos, endPos)
    end

fun tok1 startPos tok ender cs v =
    let val _ = ensurePos startPos
        val startPos = getPos ()
        val _ = advance startPos cs
        val endPos = getPos ()
        val _ = setPrev ender endPos
    in tok (v, startPos, endPos)
    end

fun prevTokenWasOnLine line = 
    case prevTokenEnd ()
    of SOME {line = tokLine, ...} => tokLine = line
     | NONE => false

fun shouldInsertSemi () =
    prevTokenWasOnLine (#line (getPos()))
    andalso prevTokenWasEnder ()

(* FIXME: If file is empty, `eof` will raise Option. *)
fun eof _ =
    let val pos = getPos ()
    in reset () (* HACK *)
     ; Tokens.EOF(pos, pos)
    end

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

\n       => (if shouldInsertSemi ()
             then tok0 startPos Tokens.SEMICOLON false yytext
             else ( advance startPos yytext
                  ; continue () ));
{ws}+    => (advance startPos yytext; continue());

"="      => (tok0 startPos Tokens.EQ false yytext);
"=>"     => (tok0 startPos Tokens.DARROW false yytext);
":"      => (tok0 startPos Tokens.COLON false yytext);
"->"     => (tok0 startPos Tokens.ARROW false yytext);
"|"      => (tok0 startPos Tokens.BAR false yytext);
".."     => (tok0 startPos Tokens.DDOT false yytext);
"&"      => (tok0 startPos Tokens.AMP false yytext);
"."      => (tok0 startPos Tokens.DOT false yytext);
","      => (tok0 startPos Tokens.COMMA false yytext);
";"      => (tok0 startPos Tokens.SEMICOLON false yytext);

"("      => (tok0 startPos Tokens.LPAREN false yytext);
")"      => (tok0 startPos Tokens.RPAREN true yytext);
"{"      => (tok0 startPos Tokens.LBRACE false yytext);
"}"      => (tok0 startPos Tokens.RBRACE true yytext);

"type"   => (tok0 startPos Tokens.TYPE false yytext);
"do"     => (tok0 startPos Tokens.DO false yytext);
"module" => (tok0 startPos Tokens.MODULE false yytext);
"interface" => (tok0 startPos Tokens.INTERFACE false yytext);
"fun"    => (tok0 startPos Tokens.FUN false yytext);
"end"    => (tok0 startPos Tokens.END true yytext);
"if"     => (tok0 startPos Tokens.IF false yytext);
"then"   => (tok0 startPos Tokens.THEN false yytext);
"else"   => (tok0 startPos Tokens.ELSE false yytext);
"True"   => (tok1 startPos Tokens.BOOL true yytext true);
"False"  => (tok1 startPos Tokens.BOOL true yytext false);
({alpha}|_)({alpha}|{digit}|_)* => (tok1 startPos Tokens.ID true yytext yytext);

{digit}+ => (tok1 startPos Tokens.INT true yytext (valOf (Int.fromString yytext)));

