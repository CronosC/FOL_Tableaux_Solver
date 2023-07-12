%--------------------------------------------------------------------------
% File     : KRS009-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 3c
% Version  : Especial.
% English  : e exists.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 3(c) [PP95]

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :   41 (   1 unt;  10 nHn;  35 RR)
%            Number of literals    :  102 (   0 equ;  53 neg)
%            Maximal clause size   :    7 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   14 (  14 usr;   0 prp; 1-2 aty)
%            Number of functors    :   13 (  13 usr;   1 con; 0-1 aty)
%            Number of variables   :   56 (   2 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    e(exist) ).

cnf(clause_2,axiom,
    ( p2least(X1)
    | ~ c(X1) ) ).

cnf(clause_3,axiom,
    ( c(X1)
    | ~ p2least(X1) ) ).

cnf(clause_4,axiom,
    ( ~ p2least(X1)
    | ~ equalish(u1r2(X1),u1r1(X1)) ) ).

cnf(clause_5,axiom,
    ( p(X1,u1r1(X1))
    | ~ p2least(X1) ) ).

cnf(clause_6,axiom,
    ( p(X1,u1r2(X1))
    | ~ p2least(X1) ) ).

cnf(clause_7,axiom,
    ( p2least(X1)
    | equalish(X3,X2)
    | ~ p(X1,X3)
    | ~ p(X1,X2) ) ).

cnf(clause_8,axiom,
    ( p1most(X1)
    | ~ d(X1) ) ).

cnf(clause_9,axiom,
    ( d(X1)
    | ~ p1most(X1) ) ).

cnf(clause_10,axiom,
    ( equalish(X3,X2)
    | ~ p1most(X1)
    | ~ p(X1,X3)
    | ~ p(X1,X2) ) ).

cnf(clause_11,axiom,
    ( p1most(X1)
    | ~ equalish(u3r2(X1),u3r1(X1)) ) ).

cnf(clause_12,axiom,
    ( p1most(X1)
    | p(X1,u3r1(X1)) ) ).

cnf(clause_13,axiom,
    ( p1most(X1)
    | p(X1,u3r2(X1)) ) ).

cnf(clause_14,axiom,
    ( c(X1)
    | d(X1)
    | ~ a(X1) ) ).

cnf(clause_15,axiom,
    ( a(X1)
    | ~ d(X1) ) ).

cnf(clause_16,axiom,
    ( a(X1)
    | ~ c(X1) ) ).

cnf(clause_17,axiom,
    ( c(X2)
    | ~ r(X1,X2) ) ).

cnf(clause_18,axiom,
    ( t(X1,X2)
    | ~ r(X1,X2) ) ).

cnf(clause_19,axiom,
    ( d(X2)
    | ~ s(X1,X2) ) ).

cnf(clause_20,axiom,
    ( t(X1,X2)
    | ~ s(X1,X2) ) ).

cnf(clause_21,axiom,
    ( s1most(X1)
    | ~ e(X1) ) ).

cnf(clause_22,axiom,
    ( r1most(X1)
    | ~ e(X1) ) ).

cnf(clause_23,axiom,
    ( t3least(X1)
    | ~ e(X1) ) ).

cnf(clause_24,axiom,
    ( a(X2)
    | ~ e(X1)
    | ~ t(X1,X2) ) ).

cnf(clause_25,axiom,
    ( e(X1)
    | ~ a(u7r1(X1))
    | ~ t3least(X1)
    | ~ r1most(X1)
    | ~ s1most(X1) ) ).

cnf(clause_26,axiom,
    ( e(X1)
    | t(X1,u7r1(X1))
    | ~ t3least(X1)
    | ~ r1most(X1)
    | ~ s1most(X1) ) ).

cnf(clause_27,axiom,
    ( ~ t3least(X1)
    | ~ equalish(u8r2(X1),u8r1(X1)) ) ).

cnf(clause_28,axiom,
    ( ~ t3least(X1)
    | ~ equalish(u8r3(X1),u8r1(X1)) ) ).

cnf(clause_29,axiom,
    ( ~ t3least(X1)
    | ~ equalish(u8r3(X1),u8r2(X1)) ) ).

cnf(clause_30,axiom,
    ( t(X1,u8r1(X1))
    | ~ t3least(X1) ) ).

cnf(clause_31,axiom,
    ( t(X1,u8r2(X1))
    | ~ t3least(X1) ) ).

cnf(clause_32,axiom,
    ( t(X1,u8r3(X1))
    | ~ t3least(X1) ) ).

cnf(clause_33,axiom,
    ( t3least(X1)
    | equalish(X4,X3)
    | equalish(X4,X2)
    | equalish(X3,X2)
    | ~ t(X1,X4)
    | ~ t(X1,X3)
    | ~ t(X1,X2) ) ).

cnf(clause_34,axiom,
    ( equalish(X3,X2)
    | ~ r1most(X1)
    | ~ r(X1,X3)
    | ~ r(X1,X2) ) ).

cnf(clause_35,axiom,
    ( r1most(X1)
    | ~ equalish(u9r2(X1),u9r1(X1)) ) ).

cnf(clause_36,axiom,
    ( r1most(X1)
    | r(X1,u9r1(X1)) ) ).

cnf(clause_37,axiom,
    ( r1most(X1)
    | r(X1,u9r2(X1)) ) ).

cnf(clause_38,axiom,
    ( equalish(X3,X2)
    | ~ s1most(X1)
    | ~ s(X1,X3)
    | ~ s(X1,X2) ) ).

cnf(clause_39,axiom,
    ( s1most(X1)
    | ~ equalish(u10r2(X1),u10r1(X1)) ) ).

cnf(clause_40,axiom,
    ( s1most(X1)
    | s(X1,u10r1(X1)) ) ).

cnf(clause_41,axiom,
    ( s1most(X1)
    | s(X1,u10r2(X1)) ) ).

%--------------------------------------------------------------------------
