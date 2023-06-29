%%%%%% DEFS %%%%%%%%%%

Nonterminals cnf_wrapperlist cnf_wrapper cnf_formula fof_wrapperlist fof_wrapper fof_formula quantor quantor_variables op_binary op_unary arglist symlist predicate  S.
Terminals start_fof start_cnf allqu exqu eq neq or and imp not sym ':' '[' ']' '(' ')' ',' '.' .
Rootsymbol S.


%%%%%% START %%%%%%%%%

S -> cnf_wrapperlist : {'and', '$1'}.
S -> fof_wrapperlist : {'and', '$1'}.


%%%%%%% CNF %%%%%%%%%%

cnf_wrapperlist -> cnf_wrapper : ['$1'].
cnf_wrapperlist -> cnf_wrapper cnf_wrapperlist : ['$1'] ++ '$2'.

cnf_wrapper -> start_cnf '(' sym ',' sym ',' cnf_formula ')' '.' : '$7'.

cnf_formula -> '(' cnf_formula ')' : '$2'.
cnf_formula -> cnf_formula op_binary cnf_formula : {'$2', ['$1', '$3']}.
cnf_formula -> op_unary cnf_formula : {'$1', '$2'}.
cnf_formula -> predicate : '$1'.
cnf_formula -> sym  : '$1'.


%%%%%%% FOF %%%%%%%%%%

fof_wrapperlist -> fof_wrapper : ['$1'].
fof_wrapperlist -> fof_wrapper fof_wrapperlist : ['$1'] ++ '$2'.

fof_wrapper -> start_fof '(' sym ',' sym ',' fof_formula ')' '.' : '$7'.

fof_formula -> '(' fof_formula ')' : '$2'.
fof_formula -> fof_formula op_binary fof_formula : {'$2', ['$1', '$3']}.
fof_formula -> op_unary fof_formula : {'$1', '$2'}.
fof_formula -> predicate : '$1'.
fof_formula -> sym  : extract_token('$1').
fof_formula -> quantor quantor_variables ':' fof_formula : {'$1', '$2', '$4'}.

quantor -> allqu : extract_atom('$1').
quantor -> exqu : extract_atom('$1').

quantor_variables -> '[' symlist ']' : '$2'.


%%%%%%% GENERAL %%%%%%%%%

predicate -> sym '(' arglist ')' : {extract_token('$1'), '$3'}.

op_binary -> eq : extract_atom('$1').
op_binary -> neq : extract_atom('$1').
op_binary -> or : extract_atom('$1').
op_binary -> and : extract_atom('$1').
op_binary -> imp : extract_atom('$1').
op_unary -> not : extract_atom('$1').

% list of symbols
symlist -> sym : [extract_token('$1')].
symlist -> sym ',' arglist : [extract_token('$1')] ++ '$3'. 

% list of predicates or symbols
arglist -> sym : [extract_token('$1')].
arglist -> predicate : ['$1'].
arglist -> sym ',' arglist : [extract_token('$1')] ++ '$3'. 
arglist -> predicate ',' arglist : ['$1'] ++ '$3'. 


%%%%%%% ERLANG %%%%%%%%%

Erlang code.
extract_token({_Token, Value}) -> Value.
extract_atom({Token, _Value}) -> Token.