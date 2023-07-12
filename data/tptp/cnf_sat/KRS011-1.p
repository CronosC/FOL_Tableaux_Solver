%--------------------------------------------------------------------------
% File     : KRS011-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 3e
% Version  : Especial.
% English  : g subsumes f.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 3(e) [PP95]

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.4.0, 0.33 v2.3.0, 0.00 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :   54 (   2 unt;  13 nHn;  54 RR)
%            Number of literals    :  179 (   0 equ; 117 neg)
%            Maximal clause size   :    7 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   18 (  18 usr;   0 prp; 1-2 aty)
%            Number of functors    :   18 (  18 usr;   1 con; 0-2 aty)
%            Number of variables   :  105 (   0 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    f(exists) ).

cnf(clause_2,negated_conjecture,
    ~ g(exists) ).

cnf(clause_3,axiom,
    ( r(X1,X2)
    | ~ r1(X1,X2) ) ).

cnf(clause_4,axiom,
    ( r(X1,X2)
    | ~ r2(X1,X2) ) ).

cnf(clause_5,axiom,
    ( r(X1,X2)
    | ~ r3(X1,X2) ) ).

cnf(clause_6,axiom,
    ( t(X1,X2)
    | ~ t1(X1,X2) ) ).

cnf(clause_7,axiom,
    ( t(X1,X2)
    | ~ t2(X1,X2) ) ).

cnf(clause_8,axiom,
    ( t(X1,X2)
    | ~ t3(X1,X2) ) ).

cnf(clause_9,axiom,
    ( ~ c(X1)
    | ~ e(X1) ) ).

cnf(clause_10,axiom,
    ( ~ c(X1)
    | ~ d(X1) ) ).

cnf(clause_11,axiom,
    ( ~ d(X1)
    | ~ e(X1) ) ).

cnf(clause_12,axiom,
    ( ~ d(X1)
    | ~ c(X1) ) ).

cnf(clause_13,axiom,
    ( ~ e(X1)
    | ~ d(X1) ) ).

cnf(clause_14,axiom,
    ( ~ e(X1)
    | ~ c(X1) ) ).

cnf(clause_15,axiom,
    ( c(u9r5(X1))
    | ~ f1(X1) ) ).

cnf(clause_16,axiom,
    ( t1(u9r4(X1),u9r5(X1))
    | ~ f1(X1) ) ).

cnf(clause_17,axiom,
    ( equalish(X5,X4)
    | equalish(X5,X3)
    | equalish(X4,X3)
    | ~ f1(X1)
    | ~ t(u9r4(X1),X5)
    | ~ t(u9r4(X1),X4)
    | ~ t(u9r4(X1),X3) ) ).

cnf(clause_18,axiom,
    ( r1(X1,u9r4(X1))
    | ~ f1(X1) ) ).

cnf(clause_19,axiom,
    ( f1(X1)
    | ~ r1(X1,X2)
    | ~ equalish(u9r2(X2,X1),u9r1(X2,X1))
    | ~ t1(X2,X6)
    | ~ c(X6) ) ).

cnf(clause_20,axiom,
    ( f1(X1)
    | ~ r1(X1,X2)
    | ~ equalish(u9r3(X2,X1),u9r1(X2,X1))
    | ~ t1(X2,X6)
    | ~ c(X6) ) ).

cnf(clause_21,axiom,
    ( f1(X1)
    | ~ r1(X1,X2)
    | ~ equalish(u9r3(X2,X1),u9r2(X2,X1))
    | ~ t1(X2,X6)
    | ~ c(X6) ) ).

cnf(clause_22,axiom,
    ( f1(X1)
    | t(X2,u9r1(X2,X1))
    | ~ r1(X1,X2)
    | ~ t1(X2,X6)
    | ~ c(X6) ) ).

cnf(clause_23,axiom,
    ( f1(X1)
    | t(X2,u9r2(X2,X1))
    | ~ r1(X1,X2)
    | ~ t1(X2,X6)
    | ~ c(X6) ) ).

cnf(clause_24,axiom,
    ( f1(X1)
    | t(X2,u9r3(X2,X1))
    | ~ r1(X1,X2)
    | ~ t1(X2,X6)
    | ~ c(X6) ) ).

cnf(clause_25,axiom,
    ( d(u10r5(X1))
    | ~ f2(X1) ) ).

cnf(clause_26,axiom,
    ( t2(u10r4(X1),u10r5(X1))
    | ~ f2(X1) ) ).

cnf(clause_27,axiom,
    ( equalish(X5,X4)
    | equalish(X5,X3)
    | equalish(X4,X3)
    | ~ f2(X1)
    | ~ t(u10r4(X1),X5)
    | ~ t(u10r4(X1),X4)
    | ~ t(u10r4(X1),X3) ) ).

cnf(clause_28,axiom,
    ( r2(X1,u10r4(X1))
    | ~ f2(X1) ) ).

cnf(clause_29,axiom,
    ( f2(X1)
    | ~ r2(X1,X2)
    | ~ equalish(u10r2(X2,X1),u10r1(X2,X1))
    | ~ t2(X2,X6)
    | ~ d(X6) ) ).

cnf(clause_30,axiom,
    ( f2(X1)
    | ~ r2(X1,X2)
    | ~ equalish(u10r3(X2,X1),u10r1(X2,X1))
    | ~ t2(X2,X6)
    | ~ d(X6) ) ).

cnf(clause_31,axiom,
    ( f2(X1)
    | ~ r2(X1,X2)
    | ~ equalish(u10r3(X2,X1),u10r2(X2,X1))
    | ~ t2(X2,X6)
    | ~ d(X6) ) ).

cnf(clause_32,axiom,
    ( f2(X1)
    | t(X2,u10r1(X2,X1))
    | ~ r2(X1,X2)
    | ~ t2(X2,X6)
    | ~ d(X6) ) ).

cnf(clause_33,axiom,
    ( f2(X1)
    | t(X2,u10r2(X2,X1))
    | ~ r2(X1,X2)
    | ~ t2(X2,X6)
    | ~ d(X6) ) ).

cnf(clause_34,axiom,
    ( f2(X1)
    | t(X2,u10r3(X2,X1))
    | ~ r2(X1,X2)
    | ~ t2(X2,X6)
    | ~ d(X6) ) ).

cnf(clause_35,axiom,
    ( e(u11r5(X1))
    | ~ f3(X1) ) ).

cnf(clause_36,axiom,
    ( t3(u11r4(X1),u11r5(X1))
    | ~ f3(X1) ) ).

cnf(clause_37,axiom,
    ( equalish(X5,X4)
    | equalish(X5,X3)
    | equalish(X4,X3)
    | ~ f3(X1)
    | ~ t(u11r4(X1),X5)
    | ~ t(u11r4(X1),X4)
    | ~ t(u11r4(X1),X3) ) ).

cnf(clause_38,axiom,
    ( r3(X1,u11r4(X1))
    | ~ f3(X1) ) ).

cnf(clause_39,axiom,
    ( f3(X1)
    | ~ r3(X1,X2)
    | ~ equalish(u11r2(X2,X1),u11r1(X2,X1))
    | ~ t3(X2,X6)
    | ~ e(X6) ) ).

cnf(clause_40,axiom,
    ( f3(X1)
    | ~ r3(X1,X2)
    | ~ equalish(u11r3(X2,X1),u11r1(X2,X1))
    | ~ t3(X2,X6)
    | ~ e(X6) ) ).

cnf(clause_41,axiom,
    ( f3(X1)
    | ~ r3(X1,X2)
    | ~ equalish(u11r3(X2,X1),u11r2(X2,X1))
    | ~ t3(X2,X6)
    | ~ e(X6) ) ).

cnf(clause_42,axiom,
    ( f3(X1)
    | t(X2,u11r1(X2,X1))
    | ~ r3(X1,X2)
    | ~ t3(X2,X6)
    | ~ e(X6) ) ).

cnf(clause_43,axiom,
    ( f3(X1)
    | t(X2,u11r2(X2,X1))
    | ~ r3(X1,X2)
    | ~ t3(X2,X6)
    | ~ e(X6) ) ).

cnf(clause_44,axiom,
    ( f3(X1)
    | t(X2,u11r3(X2,X1))
    | ~ r3(X1,X2)
    | ~ t3(X2,X6)
    | ~ e(X6) ) ).

cnf(clause_45,axiom,
    ( f3(X1)
    | ~ f(X1) ) ).

cnf(clause_46,axiom,
    ( f2(X1)
    | ~ f(X1) ) ).

cnf(clause_47,axiom,
    ( f1(X1)
    | ~ f(X1) ) ).

cnf(clause_48,axiom,
    ( f(X1)
    | ~ f1(X1)
    | ~ f2(X1)
    | ~ f3(X1) ) ).

cnf(clause_49,axiom,
    ( r2least(X1)
    | ~ g(X1) ) ).

cnf(clause_50,axiom,
    ( g(X1)
    | ~ r2least(X1) ) ).

cnf(clause_51,axiom,
    ( ~ r2least(X1)
    | ~ equalish(u14r2(X1),u14r1(X1)) ) ).

cnf(clause_52,axiom,
    ( r(X1,u14r1(X1))
    | ~ r2least(X1) ) ).

cnf(clause_53,axiom,
    ( r(X1,u14r2(X1))
    | ~ r2least(X1) ) ).

cnf(clause_54,axiom,
    ( r2least(X1)
    | equalish(X3,X2)
    | ~ r(X1,X3)
    | ~ r(X1,X2) ) ).

%--------------------------------------------------------------------------
