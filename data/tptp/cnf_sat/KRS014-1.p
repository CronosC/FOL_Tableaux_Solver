%--------------------------------------------------------------------------
% File     : KRS014-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 5a
% Version  : Especial.
% English  : e exists.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 5(a) [PP95]

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0, 0.17 v2.4.0, 0.00 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :   18 (   1 unt;   6 nHn;  18 RR)
%            Number of literals    :   57 (   0 equ;  32 neg)
%            Maximal clause size   :    5 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 1-2 aty)
%            Number of functors    :    7 (   7 usr;   1 con; 0-3 aty)
%            Number of variables   :   29 (   0 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    e(exists) ).

cnf(clause_2,axiom,
    ( s(X1,X2)
    | ~ e(X1)
    | ~ r(X1,X2) ) ).

cnf(clause_3,axiom,
    ( r(X1,X2)
    | ~ e(X1)
    | ~ s(X1,X2) ) ).

cnf(clause_4,axiom,
    ( s2exact(X1)
    | ~ e(X1) ) ).

cnf(clause_5,axiom,
    ( r1exact(X1)
    | ~ e(X1) ) ).

cnf(clause_6,axiom,
    ( e(X1)
    | s(X1,u0r1(X1))
    | r(X1,u0r1(X1))
    | ~ r1exact(X1)
    | ~ s2exact(X1) ) ).

cnf(clause_7,axiom,
    ( e(X1)
    | ~ r1exact(X1)
    | ~ s2exact(X1)
    | ~ r(X1,u0r1(X1))
    | ~ s(X1,u0r1(X1)) ) ).

cnf(clause_8,axiom,
    ( equalish(X3,u1r2(X1))
    | ~ r1exact(X1)
    | ~ r(X1,X3) ) ).

cnf(clause_9,axiom,
    ( r(X1,u1r2(X1))
    | ~ r1exact(X1) ) ).

cnf(clause_10,axiom,
    ( r1exact(X1)
    | ~ r(X1,X2)
    | ~ equalish(u1r1(X2,X1),X2) ) ).

cnf(clause_11,axiom,
    ( r1exact(X1)
    | r(X1,u1r1(X2,X1))
    | ~ r(X1,X2) ) ).

cnf(clause_12,axiom,
    ( equalish(X4,u2r3(X1))
    | equalish(X4,u2r2(X1))
    | ~ s2exact(X1)
    | ~ s(X1,X4) ) ).

cnf(clause_13,axiom,
    ( ~ s2exact(X1)
    | ~ equalish(u2r3(X1),u2r2(X1)) ) ).

cnf(clause_14,axiom,
    ( s(X1,u2r2(X1))
    | ~ s2exact(X1) ) ).

cnf(clause_15,axiom,
    ( s(X1,u2r3(X1))
    | ~ s2exact(X1) ) ).

cnf(clause_16,axiom,
    ( s2exact(X1)
    | equalish(X3,X2)
    | ~ s(X1,X3)
    | ~ s(X1,X2)
    | ~ equalish(u2r1(X3,X2,X1),X2) ) ).

cnf(clause_17,axiom,
    ( s2exact(X1)
    | equalish(X3,X2)
    | ~ s(X1,X3)
    | ~ s(X1,X2)
    | ~ equalish(u2r1(X3,X2,X1),X3) ) ).

cnf(clause_18,axiom,
    ( s2exact(X1)
    | equalish(X3,X2)
    | s(X1,u2r1(X3,X2,X1))
    | ~ s(X1,X3)
    | ~ s(X1,X2) ) ).

%--------------------------------------------------------------------------
