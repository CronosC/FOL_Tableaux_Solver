%--------------------------------------------------------------------------
% File     : KRS015-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 5b
% Version  : Especial.
% English  : e exists.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 5(b) [PP95]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v5.5.0, 0.12 v5.4.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :   26 (   1 unt;  10 nHn;  24 RR)
%            Number of literals    :   91 (   0 equ;  47 neg)
%            Maximal clause size   :    6 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    9 (   9 usr;   0 prp; 1-2 aty)
%            Number of functors    :    9 (   9 usr;   1 con; 0-1 aty)
%            Number of variables   :   41 (   8 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    e(exist) ).

cnf(clause_2,axiom,
    ( t2least(X1)
    | ~ c(X1) ) ).

cnf(clause_3,axiom,
    ( c(X1)
    | ~ t2least(X1) ) ).

cnf(clause_4,axiom,
    ( ~ t2least(X1)
    | ~ equalish(u1r2(X1),u1r1(X1)) ) ).

cnf(clause_5,axiom,
    ( t(X1,u1r1(X1))
    | ~ t2least(X1) ) ).

cnf(clause_6,axiom,
    ( t(X1,u1r2(X1))
    | ~ t2least(X1) ) ).

cnf(clause_7,axiom,
    ( t2least(X1)
    | equalish(X3,X2)
    | ~ t(X1,X3)
    | ~ t(X1,X2) ) ).

cnf(clause_8,axiom,
    ( t1most(X1)
    | ~ d(X1) ) ).

cnf(clause_9,axiom,
    ( d(X1)
    | ~ t1most(X1) ) ).

cnf(clause_10,axiom,
    ( equalish(X3,X2)
    | ~ t1most(X1)
    | ~ t(X1,X3)
    | ~ t(X1,X2) ) ).

cnf(clause_11,axiom,
    ( t1most(X1)
    | ~ equalish(u3r2(X1),u3r1(X1)) ) ).

cnf(clause_12,axiom,
    ( t1most(X1)
    | t(X1,u3r1(X1)) ) ).

cnf(clause_13,axiom,
    ( t1most(X1)
    | t(X1,u3r2(X1)) ) ).

cnf(clause_14,axiom,
    ( r(X1,u4r4(X1))
    | ~ e(X1) ) ).

cnf(clause_15,axiom,
    ( s(X1,X4)
    | ~ e(X1)
    | ~ r(X1,X4) ) ).

cnf(clause_16,axiom,
    ( r(X1,X4)
    | ~ e(X1)
    | ~ s(X1,X4) ) ).

cnf(clause_17,axiom,
    ( d(X3)
    | ~ e(X1)
    | ~ s(X1,X3) ) ).

cnf(clause_18,axiom,
    ( c(X2)
    | ~ e(X1)
    | ~ r(X1,X2) ) ).

cnf(clause_19,axiom,
    ( e(X1)
    | s(X1,u4r3(X1))
    | r(X1,u4r3(X1))
    | ~ c(u4r1(X1))
    | ~ d(u4r2(X1))
    | ~ r(X1,X5) ) ).

cnf(clause_20,axiom,
    ( e(X1)
    | ~ c(u4r1(X1))
    | ~ d(u4r2(X1))
    | ~ r(X1,u4r3(X1))
    | ~ s(X1,u4r3(X1))
    | ~ r(X1,X5) ) ).

cnf(clause_21,axiom,
    ( e(X1)
    | s(X1,u4r2(X1))
    | s(X1,u4r3(X1))
    | r(X1,u4r3(X1))
    | ~ c(u4r1(X1))
    | ~ r(X1,X5) ) ).

cnf(clause_22,axiom,
    ( e(X1)
    | s(X1,u4r2(X1))
    | ~ c(u4r1(X1))
    | ~ r(X1,u4r3(X1))
    | ~ s(X1,u4r3(X1))
    | ~ r(X1,X5) ) ).

cnf(clause_23,axiom,
    ( e(X1)
    | r(X1,u4r1(X1))
    | s(X1,u4r3(X1))
    | r(X1,u4r3(X1))
    | ~ d(u4r2(X1))
    | ~ r(X1,X5) ) ).

cnf(clause_24,axiom,
    ( e(X1)
    | r(X1,u4r1(X1))
    | ~ d(u4r2(X1))
    | ~ r(X1,u4r3(X1))
    | ~ s(X1,u4r3(X1))
    | ~ r(X1,X5) ) ).

cnf(clause_25,axiom,
    ( e(X1)
    | r(X1,u4r1(X1))
    | s(X1,u4r2(X1))
    | s(X1,u4r3(X1))
    | r(X1,u4r3(X1))
    | ~ r(X1,X5) ) ).

cnf(clause_26,axiom,
    ( e(X1)
    | r(X1,u4r1(X1))
    | s(X1,u4r2(X1))
    | ~ r(X1,u4r3(X1))
    | ~ s(X1,u4r3(X1))
    | ~ r(X1,X5) ) ).

%--------------------------------------------------------------------------
