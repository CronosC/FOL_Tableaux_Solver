%--------------------------------------------------------------------------
% File     : KRS013-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 4b
% Version  : Especial.
% English  : f subsumes e.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 4(b) [PP95]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :   33 (   2 unt;  12 nHn;  26 RR)
%            Number of literals    :   82 (   0 equ;  38 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   12 (  12 usr;   0 prp; 1-2 aty)
%            Number of functors    :   12 (  12 usr;   1 con; 0-1 aty)
%            Number of variables   :   42 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    e(exist) ).

cnf(clause_2,negated_conjecture,
    ~ f(exist) ).

cnf(clause_3,axiom,
    ( t2least(X1)
    | ~ c(X1) ) ).

cnf(clause_4,axiom,
    ( c(X1)
    | ~ t2least(X1) ) ).

cnf(clause_5,axiom,
    ( ~ t2least(X1)
    | ~ equalish(u1r2(X1),u1r1(X1)) ) ).

cnf(clause_6,axiom,
    ( t(X1,u1r1(X1))
    | ~ t2least(X1) ) ).

cnf(clause_7,axiom,
    ( t(X1,u1r2(X1))
    | ~ t2least(X1) ) ).

cnf(clause_8,axiom,
    ( t2least(X1)
    | equalish(X3,X2)
    | ~ t(X1,X3)
    | ~ t(X1,X2) ) ).

cnf(clause_9,axiom,
    ( t1most(X1)
    | ~ d(X1) ) ).

cnf(clause_10,axiom,
    ( d(X1)
    | ~ t1most(X1) ) ).

cnf(clause_11,axiom,
    ( equalish(X3,X2)
    | ~ t1most(X1)
    | ~ t(X1,X3)
    | ~ t(X1,X2) ) ).

cnf(clause_12,axiom,
    ( t1most(X1)
    | ~ equalish(u3r2(X1),u3r1(X1)) ) ).

cnf(clause_13,axiom,
    ( t1most(X1)
    | t(X1,u3r1(X1)) ) ).

cnf(clause_14,axiom,
    ( t1most(X1)
    | t(X1,u3r2(X1)) ) ).

cnf(clause_15,axiom,
    ( d(X3)
    | ~ e(X1)
    | ~ r(X1,X3) ) ).

cnf(clause_16,axiom,
    ( c(X2)
    | ~ e(X1)
    | ~ r(X1,X2)
    | ~ s2least(X2) ) ).

cnf(clause_17,axiom,
    ( e(X1)
    | ~ c(u4r1(X1))
    | ~ d(u4r2(X1)) ) ).

cnf(clause_18,axiom,
    ( e(X1)
    | r(X1,u4r2(X1))
    | ~ c(u4r1(X1)) ) ).

cnf(clause_19,axiom,
    ( e(X1)
    | s2least(u4r1(X1))
    | ~ d(u4r2(X1)) ) ).

cnf(clause_20,axiom,
    ( e(X1)
    | s2least(u4r1(X1))
    | r(X1,u4r2(X1)) ) ).

cnf(clause_21,axiom,
    ( e(X1)
    | r(X1,u4r1(X1))
    | ~ d(u4r2(X1)) ) ).

cnf(clause_22,axiom,
    ( e(X1)
    | r(X1,u4r1(X1))
    | r(X1,u4r2(X1)) ) ).

cnf(clause_23,axiom,
    ( ~ s2least(X1)
    | ~ equalish(u5r2(X1),u5r1(X1)) ) ).

cnf(clause_24,axiom,
    ( s(X1,u5r1(X1))
    | ~ s2least(X1) ) ).

cnf(clause_25,axiom,
    ( s(X1,u5r2(X1))
    | ~ s2least(X1) ) ).

cnf(clause_26,axiom,
    ( s2least(X1)
    | equalish(X3,X2)
    | ~ s(X1,X3)
    | ~ s(X1,X2) ) ).

cnf(clause_27,axiom,
    ( s1most(X2)
    | ~ f(X1)
    | ~ r(X1,X2) ) ).

cnf(clause_28,axiom,
    ( f(X1)
    | ~ s1most(u6r1(X1)) ) ).

cnf(clause_29,axiom,
    ( f(X1)
    | r(X1,u6r1(X1)) ) ).

cnf(clause_30,axiom,
    ( equalish(X3,X2)
    | ~ s1most(X1)
    | ~ s(X1,X3)
    | ~ s(X1,X2) ) ).

cnf(clause_31,axiom,
    ( s1most(X1)
    | ~ equalish(u7r2(X1),u7r1(X1)) ) ).

cnf(clause_32,axiom,
    ( s1most(X1)
    | s(X1,u7r1(X1)) ) ).

cnf(clause_33,axiom,
    ( s1most(X1)
    | s(X1,u7r2(X1)) ) ).

%--------------------------------------------------------------------------
