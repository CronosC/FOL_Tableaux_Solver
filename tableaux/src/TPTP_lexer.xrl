Definitions.

SYM          = [A-Za-z0-9_]*
REMOVE       = [\s\t\n\r]
COMMENT      = %.*\n


Rules.

negated_conjecture : {token, {neg_conj, TokenChars}}.
fof           : {token, {start_fof, TokenChars}}.
cnf           : {token, {start_cnf, TokenChars}}.
{SYM}         : {token, {sym, to_atom(TokenChars)}}.
\(            : {token, {'(', TokenChars}}.
\)            : {token, {')', TokenChars}}.
\[            : {token, {'[', TokenChars}}.
\]            : {token, {']', TokenChars}}.
,             : {token, {',', TokenChars}}.
\.            : {token, {'.', TokenChars}}.
\:            : {token, {':', TokenChars}}.
~             : {token, {'not', TokenChars}}.
=             : {token, {'eq', TokenChars}}.
!=            : {token, {'neq', TokenChars}}.
=>            : {token, {'imp', TokenChars}}.
\|            : {token, {'or', TokenChars}}.
\&            : {token, {'and', TokenChars}}.
\?            : {token, {'exqu', TokenChars}}.
\!            : {token, {'allqu', TokenChars}}.
{REMOVE}+     : skip_token.
{COMMENT}+    : skip_token.


Erlang code.

to_atom(Chars) ->
    list_to_atom(Chars).
