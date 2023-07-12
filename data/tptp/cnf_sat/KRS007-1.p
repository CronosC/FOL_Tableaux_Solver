%--------------------------------------------------------------------------
% File     : KRS007-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 3a
% Version  : Especial.
% English  : f subsumes e.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 3(a) [PP95]

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.4.0, 0.33 v2.3.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :   26 (   2 unt;   4 nHn;  24 RR)
%            Number of literals    :   60 (   0 equ;  33 neg)
%            Maximal clause size   :    6 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   10 (  10 usr;   0 prp; 1-2 aty)
%            Number of functors    :   10 (  10 usr;   1 con; 0-1 aty)
%            Number of variables   :   33 (   1 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    e(exist) ).

cnf(clause_2,negated_conjecture,
    ~ f(exist) ).

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
    ( d(u4r3(X1))
    | ~ e(X1) ) ).

cnf(clause_16,axiom,
    ( r(X1,u4r3(X1))
    | ~ e(X1) ) ).

cnf(clause_17,axiom,
    ( c(u4r2(X1))
    | ~ e(X1) ) ).

cnf(clause_18,axiom,
    ( r(X1,u4r2(X1))
    | ~ e(X1) ) ).

cnf(clause_19,axiom,
    ( r(X1,u4r1(X1))
    | ~ e(X1) ) ).

cnf(clause_20,axiom,
    ( e(X1)
    | ~ r(X1,X2)
    | ~ r(X1,X3)
    | ~ c(X3)
    | ~ r(X1,X4)
    | ~ d(X4) ) ).

cnf(clause_21,axiom,
    ( r2least(X1)
    | ~ f(X1) ) ).

cnf(clause_22,axiom,
    ( f(X1)
    | ~ r2least(X1) ) ).

cnf(clause_23,axiom,
    ( ~ r2least(X1)
    | ~ equalish(u6r2(X1),u6r1(X1)) ) ).

cnf(clause_24,axiom,
    ( r(X1,u6r1(X1))
    | ~ r2least(X1) ) ).

cnf(clause_25,axiom,
    ( r(X1,u6r2(X1))
    | ~ r2least(X1) ) ).

cnf(clause_26,axiom,
    ( r2least(X1)
    | equalish(X3,X2)
    | ~ r(X1,X3)
    | ~ r(X1,X2) ) ).

%--------------------------------------------------------------------------
