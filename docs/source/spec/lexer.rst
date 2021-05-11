*****************
Lexical Structure
*****************

========
Encoding
========

Broom source code must be encoded in UTF-8.

=========================
Lexical Program Structure
=========================

Lexically, a program is just a sequence of tokens and whitespace:

.. math::
    programTokens \rightarrow (\mathrm{TOKEN} \, | \, \mathrm{WHITESPACE})^*

------
Tokens
------

.. math::
    \mathrm{TOKEN} &\rightarrow \mathrm{DELIMITER} \; | \; \mathrm{SEPARATOR}
            \; | \; \mathrm{DEFINER} \; | \; \mathrm{ARROW} \\
        &\quad | \; \textbf{||} \; | \; \textbf{&&} \; | \; \mathrm{COMPARISON}
            \; | \; \mathrm{ADDITIVE} \; | \; \mathrm{MULTIPLICATIVE} \\
        &\quad | \; \textbf{.} \\
        &\quad | \; \mathrm{IDENTIFIER} \; | \; \mathrm{INTRINSIC} \; | \; \mathrm{WILDCARD} \\
        &\quad | \; \mathrm{LITERAL} \\
    \mathrm{DELIMITER} &\rightarrow \textbf{(} \; | \; \textbf{)} \; | \; \textbf{[} \; | \; \textbf{]}
        \; | \; \textbf{\{} \; | \; \textbf{\}} \\
    \mathrm{SEPARATOR} &\rightarrow \; \textbf{,} \; | \; \textbf{;} \; | \; \textbf{|} \\
    \mathrm{DEFINER} &\rightarrow \; \textbf{=} \; | \; \textbf{:} \\
    \mathrm{ARROW} &\rightarrow \textbf{-!} \; | \; \textbf{->} \; | \; \textbf{=>} \; | \; \textbf{<-} \\
    \mathrm{ADDITIVE} &\rightarrow \textbf{+} \; | \; \textbf{-} \\
    \mathrm{MULTIPLICATIVE} &\rightarrow \textbf{*} \; | \; \textbf{/} \\
    \mathrm{COMPARISON} &\rightarrow \textbf{<} \; | \; \textbf{<=} \; | \; \textbf{==}
        \; | \; \textbf{>=} \; | \; \textbf{>}

----------
Whitespace
----------

.. math::
    \mathrm{WHITESPACE} &\rightarrow \mathrm{WHITESTUFF} \\
    \mathrm{WHITESTUFF} &\rightarrow \mathrm{COMMENT} \, | \, \mathrm{UNI\_WHITE} \\
    \mathrm{COMMENT} &\rightarrow \textbf{--} \; [^\wedge\textbf{\\n}]^* \; \textbf{\\n}

