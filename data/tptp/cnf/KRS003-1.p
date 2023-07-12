%--------------------------------------------------------------------------
% File     : KRS003-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 1c
% Version  : Especial.
% English  : e and f exist.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 1(c) [PP95]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :   16 (   2 unt;   3 nHn;  14 RR)
%            Number of literals    :   34 (   0 equ;  16 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    8 (   8 usr;   0 prp; 1-2 aty)
%            Number of functors    :    5 (   5 usr;   1 con; 0-1 aty)
%            Number of variables   :   18 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    e(exist) ).

cnf(clause_2,negated_conjecture,
    f(exist) ).

cnf(clause_3,axiom,
    ( s2least(X1)
    | ~ c(X1) ) ).

cnf(clause_4,axiom,
    ( c(X1)
    | ~ s2least(X1) ) ).

cnf(clause_5,axiom,
    ( ~ s2least(X1)
    | ~ equalish(u1r2(X1),u1r1(X1)) ) ).

cnf(clause_6,axiom,
    ( s(X1,u1r1(X1))
    | ~ s2least(X1) ) ).

cnf(clause_7,axiom,
    ( s(X1,u1r2(X1))
    | ~ s2least(X1) ) ).

cnf(clause_8,axiom,
    ( s2least(X1)
    | equalish(X3,X2)
    | ~ s(X1,X3)
    | ~ s(X1,X2) ) ).

cnf(clause_9,axiom,
    ( s1most(X1)
    | ~ d(X1) ) ).

cnf(clause_10,axiom,
    ( d(X1)
    | ~ s1most(X1) ) ).

cnf(clause_11,axiom,
    ( equalish(X3,X2)
    | ~ s1most(X1)
    | ~ s(X1,X3)
    | ~ s(X1,X2) ) ).

cnf(clause_12,axiom,
    ( s1most(X1)
    | ~ equalish(u3r2(X1),u3r1(X1)) ) ).

cnf(clause_13,axiom,
    ( s1most(X1)
    | s(X1,u3r1(X1)) ) ).

cnf(clause_14,axiom,
    ( s1most(X1)
    | s(X1,u3r2(X1)) ) ).

cnf(clause_15,axiom,
    ( c(X1)
    | ~ e(X1) ) ).

cnf(clause_16,axiom,
    ( d(X1)
    | ~ f(X1) ) ).

%--------------------------------------------------------------------------
