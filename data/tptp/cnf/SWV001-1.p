%--------------------------------------------------------------------------
% File     : SWV001-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Software Verification
% Problem  : PV1
% Version  : Especial.
% English  : These "clauses arose in a natural manner from work done in
%            program verification" [MOW76] p.779.

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [MOW76]
% Names    : PV1 [MOW76]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :   14 (   2 unt;   2 nHn;  12 RR)
%            Number of literals    :   36 (   0 equ;  22 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 2-3 aty)
%            Number of functors    :    3 (   3 usr;   3 con; 0-0 aty)
%            Number of variables   :   30 (   2 sgn)
% SPC      : CNF_UNS_EPR_NEQ_NHN

% Comments : This problem was contributed to [MOW76] by E. McCharen. The
%            axioms are incomplete.
%--------------------------------------------------------------------------
cnf(less_or_equal_substitution1,axiom,
    ( ~ equalish(X,Y)
    | ~ less_or_equalish(X,Z)
    | less_or_equalish(Y,Z) ) ).

cnf(less_or_equal_substitution2,axiom,
    ( ~ equalish(X,Y)
    | ~ less_or_equalish(Z,X)
    | less_or_equalish(Z,Y) ) ).

cnf(clause_1,axiom,
    ( ~ q1(X,Y,Z)
    | ~ less_or_equalish(X,Y)
    | q2(X,Y,Z) ) ).

cnf(clause_2,axiom,
    ( ~ q1(X,Y,Z)
    | less_or_equalish(X,Y)
    | q3(X,Y,Z) ) ).

cnf(clause_3,axiom,
    ( ~ q2(X,Y,Z)
    | q4(X,Y,Y) ) ).

cnf(clause_4,axiom,
    ( ~ q3(X,Y,Z)
    | q4(X,Y,X) ) ).

cnf(less_or_equal_reflexivity,axiom,
    less_or_equalish(X,X) ).

cnf(less_or_equal_implies_equal,axiom,
    ( ~ less_or_equalish(X,Y)
    | ~ less_or_equalish(Y,X)
    | equalish(X,Y) ) ).

cnf(transitivity_of_less_or_equal,axiom,
    ( ~ less_or_equalish(X,Y)
    | ~ less_or_equalish(Y,Z)
    | less_or_equalish(X,Z) ) ).

cnf(all_less_or_equal,axiom,
    ( less_or_equalish(X,Y)
    | less_or_equalish(Y,X) ) ).

cnf(equal_implies_less_or_equal,axiom,
    ( less_or_equalish(X,Y)
    | ~ equalish(X,Y) ) ).

cnf(clause_5,negated_conjecture,
    q1(a,b,c) ).

cnf(clause_6,negated_conjecture,
    ( ~ q4(a,b,W)
    | ~ less_or_equalish(a,W)
    | ~ less_or_equalish(b,W)
    | ~ less_or_equalish(W,a) ) ).

cnf(clause_7,negated_conjecture,
    ( ~ q4(a,b,W)
    | ~ less_or_equalish(a,W)
    | ~ less_or_equalish(b,W)
    | ~ less_or_equalish(W,b) ) ).

%--------------------------------------------------------------------------
