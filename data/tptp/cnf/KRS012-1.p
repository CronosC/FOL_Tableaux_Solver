%--------------------------------------------------------------------------
% File     : KRS012-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 4a
% Version  : Especial.
% English  : f subsumes c.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 4(a) [PP95]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :   13 (   2 unt;   6 nHn;  10 RR)
%            Number of literals    :   34 (   0 equ;  14 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    5 (   5 usr;   0 prp; 1-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-1 aty)
%            Number of variables   :   14 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    c(exists) ).

cnf(clause_2,negated_conjecture,
    ~ f(exists) ).

cnf(clause_3,axiom,
    ( e(X3)
    | ~ c(X1)
    | ~ r(X1,X3)
    | ~ d(X3) ) ).

cnf(clause_4,axiom,
    ( d(X2)
    | ~ c(X1)
    | ~ r(X1,X2) ) ).

cnf(clause_5,axiom,
    ( c(X1)
    | ~ d(u0r1(X1))
    | ~ e(u0r2(X1)) ) ).

cnf(clause_6,axiom,
    ( c(X1)
    | d(u0r2(X1))
    | ~ d(u0r1(X1)) ) ).

cnf(clause_7,axiom,
    ( c(X1)
    | r(X1,u0r2(X1))
    | ~ d(u0r1(X1)) ) ).

cnf(clause_8,axiom,
    ( c(X1)
    | r(X1,u0r1(X1))
    | ~ e(u0r2(X1)) ) ).

cnf(clause_9,axiom,
    ( c(X1)
    | r(X1,u0r1(X1))
    | d(u0r2(X1)) ) ).

cnf(clause_10,axiom,
    ( c(X1)
    | r(X1,u0r1(X1))
    | r(X1,u0r2(X1)) ) ).

cnf(clause_11,axiom,
    ( e(X2)
    | ~ f(X1)
    | ~ r(X1,X2) ) ).

cnf(clause_12,axiom,
    ( f(X1)
    | ~ e(u1r1(X1)) ) ).

cnf(clause_13,axiom,
    ( f(X1)
    | r(X1,u1r1(X1)) ) ).

%--------------------------------------------------------------------------
