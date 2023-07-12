%--------------------------------------------------------------------------
% File     : KRS008-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 3b
% Version  : Especial.
% English  : f subsumes e.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 3(b) [PP95]

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0, 0.33 v2.2.1, 0.75 v2.2.0, 0.67 v2.1.0
% Syntax   : Number of clauses     :   54 (   2 unt;  31 nHn;  33 RR)
%            Number of literals    :  152 (   0 equ;  52 neg)
%            Maximal clause size   :    7 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   10 (  10 usr;   0 prp; 1-2 aty)
%            Number of functors    :   14 (  14 usr;   1 con; 0-1 aty)
%            Number of variables   :   65 (   0 sgn)
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
    ( d(u4r2(X1))
    | ~ e(X1) ) ).

cnf(clause_16,axiom,
    ( r(X1,u4r2(X1))
    | ~ e(X1) ) ).

cnf(clause_17,axiom,
    ( c(u4r1(X1))
    | ~ e(X1) ) ).

cnf(clause_18,axiom,
    ( r(X1,u4r1(X1))
    | ~ e(X1) ) ).

cnf(clause_19,axiom,
    ( r2most(X1)
    | ~ e(X1) ) ).

cnf(clause_20,axiom,
    ( e(X1)
    | ~ r2most(X1)
    | ~ r(X1,X2)
    | ~ c(X2)
    | ~ r(X1,X3)
    | ~ d(X3) ) ).

cnf(clause_21,axiom,
    ( equalish(X4,X3)
    | equalish(X4,X2)
    | equalish(X3,X2)
    | ~ r2most(X1)
    | ~ r(X1,X4)
    | ~ r(X1,X3)
    | ~ r(X1,X2) ) ).

cnf(clause_22,axiom,
    ( r2most(X1)
    | ~ equalish(u5r2(X1),u5r1(X1)) ) ).

cnf(clause_23,axiom,
    ( r2most(X1)
    | ~ equalish(u5r3(X1),u5r1(X1)) ) ).

cnf(clause_24,axiom,
    ( r2most(X1)
    | ~ equalish(u5r3(X1),u5r2(X1)) ) ).

cnf(clause_25,axiom,
    ( r2most(X1)
    | r(X1,u5r1(X1)) ) ).

cnf(clause_26,axiom,
    ( r2most(X1)
    | r(X1,u5r2(X1)) ) ).

cnf(clause_27,axiom,
    ( r2most(X1)
    | r(X1,u5r3(X1)) ) ).

cnf(clause_28,axiom,
    ( equalish(X5,X4)
    | ~ f(X1)
    | ~ r(X1,X5)
    | ~ r(X1,X4)
    | ~ d(X5)
    | ~ d(X4) ) ).

cnf(clause_29,axiom,
    ( equalish(X3,X2)
    | ~ f(X1)
    | ~ r(X1,X3)
    | ~ r(X1,X2)
    | ~ c(X3)
    | ~ c(X2) ) ).

cnf(clause_30,axiom,
    ( f(X1)
    | ~ equalish(u6r2(X1),u6r1(X1))
    | ~ equalish(u6r4(X1),u6r3(X1)) ) ).

cnf(clause_31,axiom,
    ( f(X1)
    | d(u6r3(X1))
    | ~ equalish(u6r2(X1),u6r1(X1)) ) ).

cnf(clause_32,axiom,
    ( f(X1)
    | d(u6r4(X1))
    | ~ equalish(u6r2(X1),u6r1(X1)) ) ).

cnf(clause_33,axiom,
    ( f(X1)
    | r(X1,u6r3(X1))
    | ~ equalish(u6r2(X1),u6r1(X1)) ) ).

cnf(clause_34,axiom,
    ( f(X1)
    | r(X1,u6r4(X1))
    | ~ equalish(u6r2(X1),u6r1(X1)) ) ).

cnf(clause_35,axiom,
    ( f(X1)
    | c(u6r1(X1))
    | ~ equalish(u6r4(X1),u6r3(X1)) ) ).

cnf(clause_36,axiom,
    ( f(X1)
    | c(u6r1(X1))
    | d(u6r3(X1)) ) ).

cnf(clause_37,axiom,
    ( f(X1)
    | c(u6r1(X1))
    | d(u6r4(X1)) ) ).

cnf(clause_38,axiom,
    ( f(X1)
    | c(u6r1(X1))
    | r(X1,u6r3(X1)) ) ).

cnf(clause_39,axiom,
    ( f(X1)
    | c(u6r1(X1))
    | r(X1,u6r4(X1)) ) ).

cnf(clause_40,axiom,
    ( f(X1)
    | c(u6r2(X1))
    | ~ equalish(u6r4(X1),u6r3(X1)) ) ).

cnf(clause_41,axiom,
    ( f(X1)
    | c(u6r2(X1))
    | d(u6r3(X1)) ) ).

cnf(clause_42,axiom,
    ( f(X1)
    | c(u6r2(X1))
    | d(u6r4(X1)) ) ).

cnf(clause_43,axiom,
    ( f(X1)
    | c(u6r2(X1))
    | r(X1,u6r3(X1)) ) ).

cnf(clause_44,axiom,
    ( f(X1)
    | c(u6r2(X1))
    | r(X1,u6r4(X1)) ) ).

cnf(clause_45,axiom,
    ( f(X1)
    | r(X1,u6r1(X1))
    | ~ equalish(u6r4(X1),u6r3(X1)) ) ).

cnf(clause_46,axiom,
    ( f(X1)
    | r(X1,u6r1(X1))
    | d(u6r3(X1)) ) ).

cnf(clause_47,axiom,
    ( f(X1)
    | r(X1,u6r1(X1))
    | d(u6r4(X1)) ) ).

cnf(clause_48,axiom,
    ( f(X1)
    | r(X1,u6r1(X1))
    | r(X1,u6r3(X1)) ) ).

cnf(clause_49,axiom,
    ( f(X1)
    | r(X1,u6r1(X1))
    | r(X1,u6r4(X1)) ) ).

cnf(clause_50,axiom,
    ( f(X1)
    | r(X1,u6r2(X1))
    | ~ equalish(u6r4(X1),u6r3(X1)) ) ).

cnf(clause_51,axiom,
    ( f(X1)
    | r(X1,u6r2(X1))
    | d(u6r3(X1)) ) ).

cnf(clause_52,axiom,
    ( f(X1)
    | r(X1,u6r2(X1))
    | d(u6r4(X1)) ) ).

cnf(clause_53,axiom,
    ( f(X1)
    | r(X1,u6r2(X1))
    | r(X1,u6r3(X1)) ) ).

cnf(clause_54,axiom,
    ( f(X1)
    | r(X1,u6r2(X1))
    | r(X1,u6r4(X1)) ) ).

%--------------------------------------------------------------------------
