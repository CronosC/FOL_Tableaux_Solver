%--------------------------------------------------------------------------
% File     : SWV009-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Software Verification
% Problem  : A condition from Hoare's FIND program
% Version  : Especial.
% English  :

% Refs     : [Ble77] Bledsoe (1977), Non-resolution Theorem Proving
%          : [Pla82] Plaisted (1982), A Simplified Problem Reduction Format
% Source   : [Pla82]
% Names    : Hoares FIND [Ble77]
%          : Problem 5.5 [Pla82]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :    9 (   5 unt;   1 nHn;   8 RR)
%            Number of literals    :   20 (   0 equ;  11 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    7 (   7 usr;   6 con; 0-1 aty)
%            Number of variables   :    8 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    ( less_or_equal(X,Y)
    | less(Y,X) ) ).

cnf(clause_2,negated_conjecture,
    less(j,i) ).

cnf(clause_3,negated_conjecture,
    less_or_equal(m,p) ).

cnf(clause_4,negated_conjecture,
    less_or_equal(p,q) ).

cnf(clause_5,negated_conjecture,
    less_or_equal(q,n) ).

cnf(clause_6,negated_conjecture,
    ( ~ less_or_equal(m,X)
    | ~ less(X,i)
    | ~ less(j,Y)
    | ~ less_or_equal(Y,n)
    | less_or_equal(a(X),a(Y)) ) ).

cnf(clause_7,negated_conjecture,
    ( ~ less_or_equal(m,X)
    | ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,j)
    | less_or_equal(a(X),a(Y)) ) ).

cnf(clause_8,negated_conjecture,
    ( ~ less_or_equal(i,X)
    | ~ less_or_equal(X,Y)
    | ~ less_or_equal(Y,n)
    | less_or_equal(a(X),a(Y)) ) ).

cnf(clause_9,negated_conjecture,
    ~ less_or_equal(a(p),a(q)) ).

%--------------------------------------------------------------------------
