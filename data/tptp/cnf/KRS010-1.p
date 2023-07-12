%--------------------------------------------------------------------------
% File     : KRS010-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 3d
% Version  : Especial.
% English  : f subsumes e.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 3(d) [PP95]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.3.0, 0.14 v6.2.0, 0.00 v2.5.0, 0.20 v2.4.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :   31 (   2 unt;  12 nHn;  31 RR)
%            Number of literals    :   95 (   0 equ;  51 neg)
%            Maximal clause size   :    7 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    8 (   8 usr;   0 prp; 1-2 aty)
%            Number of functors    :    9 (   9 usr;   1 con; 0-1 aty)
%            Number of variables   :   37 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    e(exist) ).

cnf(clause_2,negated_conjecture,
    ~ f(exist) ).

cnf(clause_3,axiom,
    ( c(X1)
    | d(X1)
    | ~ a(X1) ) ).

cnf(clause_4,axiom,
    ( a(X1)
    | ~ d(X1) ) ).

cnf(clause_5,axiom,
    ( a(X1)
    | ~ c(X1) ) ).

cnf(clause_6,axiom,
    ( equalish(X4,X3)
    | ~ e(X1)
    | ~ r(X1,X4)
    | ~ r(X1,X3)
    | ~ c(X4)
    | ~ c(X3) ) ).

cnf(clause_7,axiom,
    ( r3least(X1)
    | ~ e(X1) ) ).

cnf(clause_8,axiom,
    ( a(X2)
    | ~ e(X1)
    | ~ r(X1,X2) ) ).

cnf(clause_9,axiom,
    ( e(X1)
    | ~ a(u1r1(X1))
    | ~ r3least(X1)
    | ~ equalish(u1r3(X1),u1r2(X1)) ) ).

cnf(clause_10,axiom,
    ( e(X1)
    | c(u1r2(X1))
    | ~ a(u1r1(X1))
    | ~ r3least(X1) ) ).

cnf(clause_11,axiom,
    ( e(X1)
    | c(u1r3(X1))
    | ~ a(u1r1(X1))
    | ~ r3least(X1) ) ).

cnf(clause_12,axiom,
    ( e(X1)
    | r(X1,u1r2(X1))
    | ~ a(u1r1(X1))
    | ~ r3least(X1) ) ).

cnf(clause_13,axiom,
    ( e(X1)
    | r(X1,u1r3(X1))
    | ~ a(u1r1(X1))
    | ~ r3least(X1) ) ).

cnf(clause_14,axiom,
    ( e(X1)
    | r(X1,u1r1(X1))
    | ~ r3least(X1)
    | ~ equalish(u1r3(X1),u1r2(X1)) ) ).

cnf(clause_15,axiom,
    ( e(X1)
    | r(X1,u1r1(X1))
    | c(u1r2(X1))
    | ~ r3least(X1) ) ).

cnf(clause_16,axiom,
    ( e(X1)
    | r(X1,u1r1(X1))
    | c(u1r3(X1))
    | ~ r3least(X1) ) ).

cnf(clause_17,axiom,
    ( e(X1)
    | r(X1,u1r1(X1))
    | r(X1,u1r2(X1))
    | ~ r3least(X1) ) ).

cnf(clause_18,axiom,
    ( e(X1)
    | r(X1,u1r1(X1))
    | r(X1,u1r3(X1))
    | ~ r3least(X1) ) ).

cnf(clause_19,axiom,
    ( ~ r3least(X1)
    | ~ equalish(u2r2(X1),u2r1(X1)) ) ).

cnf(clause_20,axiom,
    ( ~ r3least(X1)
    | ~ equalish(u2r3(X1),u2r1(X1)) ) ).

cnf(clause_21,axiom,
    ( ~ r3least(X1)
    | ~ equalish(u2r3(X1),u2r2(X1)) ) ).

cnf(clause_22,axiom,
    ( r(X1,u2r1(X1))
    | ~ r3least(X1) ) ).

cnf(clause_23,axiom,
    ( r(X1,u2r2(X1))
    | ~ r3least(X1) ) ).

cnf(clause_24,axiom,
    ( r(X1,u2r3(X1))
    | ~ r3least(X1) ) ).

cnf(clause_25,axiom,
    ( r3least(X1)
    | equalish(X4,X3)
    | equalish(X4,X2)
    | equalish(X3,X2)
    | ~ r(X1,X4)
    | ~ r(X1,X3)
    | ~ r(X1,X2) ) ).

cnf(clause_26,axiom,
    ( d(u3r1(X1))
    | ~ f(X1) ) ).

cnf(clause_27,axiom,
    ( d(u3r2(X1))
    | ~ f(X1) ) ).

cnf(clause_28,axiom,
    ( ~ f(X1)
    | ~ equalish(u3r2(X1),u3r1(X1)) ) ).

cnf(clause_29,axiom,
    ( r(X1,u3r1(X1))
    | ~ f(X1) ) ).

cnf(clause_30,axiom,
    ( r(X1,u3r2(X1))
    | ~ f(X1) ) ).

cnf(clause_31,axiom,
    ( f(X1)
    | equalish(X3,X2)
    | ~ r(X1,X3)
    | ~ r(X1,X2)
    | ~ d(X3)
    | ~ d(X2) ) ).

%--------------------------------------------------------------------------
