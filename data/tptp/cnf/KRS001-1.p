%--------------------------------------------------------------------------
% File     : KRS001-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 1a
% Version  : Especial.
% English  : e exists.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 1(a) [PP95]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :   16 (   1 unt;   3 nHn;  14 RR)
%            Number of literals    :   36 (   0 equ;  18 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    7 (   7 usr;   0 prp; 1-2 aty)
%            Number of functors    :    5 (   5 usr;   1 con; 0-1 aty)
%            Number of variables   :   19 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    e(exist) ).

cnf(clause_2,axiom,
    ( r2least(X1)
    | ~ c(X1) ) ).

cnf(clause_3,axiom,
    ( c(X1)
    | ~ r2least(X1) ) ).

cnf(clause_4,axiom,
    ( ~ r2least(X1)
    | ~ equalish(u1r2(X1),u1r1(X1)) ) ).

cnf(clause_5,axiom,
    ( r(X1,u1r1(X1))
    | ~ r2least(X1) ) ).

cnf(clause_6,axiom,
    ( r(X1,u1r2(X1))
    | ~ r2least(X1) ) ).

cnf(clause_7,axiom,
    ( r2least(X1)
    | equalish(X3,X2)
    | ~ r(X1,X3)
    | ~ r(X1,X2) ) ).

cnf(clause_8,axiom,
    ( r1most(X1)
    | ~ d(X1) ) ).

cnf(clause_9,axiom,
    ( d(X1)
    | ~ r1most(X1) ) ).

cnf(clause_10,axiom,
    ( equalish(X3,X2)
    | ~ r1most(X1)
    | ~ r(X1,X3)
    | ~ r(X1,X2) ) ).

cnf(clause_11,axiom,
    ( r1most(X1)
    | ~ equalish(u3r2(X1),u3r1(X1)) ) ).

cnf(clause_12,axiom,
    ( r1most(X1)
    | r(X1,u3r1(X1)) ) ).

cnf(clause_13,axiom,
    ( r1most(X1)
    | r(X1,u3r2(X1)) ) ).

cnf(clause_14,axiom,
    ( d(X1)
    | ~ e(X1) ) ).

cnf(clause_15,axiom,
    ( c(X1)
    | ~ e(X1) ) ).

cnf(clause_16,axiom,
    ( e(X1)
    | ~ c(X1)
    | ~ d(X1) ) ).

%--------------------------------------------------------------------------
