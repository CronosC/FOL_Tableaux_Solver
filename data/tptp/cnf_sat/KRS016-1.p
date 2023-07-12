%--------------------------------------------------------------------------
% File     : KRS016-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 5c
% Version  : Especial.
% English  : c and d exist.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 5(c) [PP95]

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :   19 (   2 unt;   7 nHn;  15 RR)
%            Number of literals    :   49 (   0 equ;  23 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    7 (   7 usr;   0 prp; 1-2 aty)
%            Number of functors    :    7 (   7 usr;   1 con; 0-1 aty)
%            Number of variables   :   24 (   0 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    c(exist) ).

cnf(clause_2,negated_conjecture,
    d(exist) ).

cnf(clause_3,axiom,
    ( s(X1,X2)
    | ~ c(X1)
    | ~ r(X1,X2) ) ).

cnf(clause_4,axiom,
    ( r(X1,X2)
    | ~ c(X1)
    | ~ s(X1,X2) ) ).

cnf(clause_5,axiom,
    ( r1most(X1)
    | ~ c(X1) ) ).

cnf(clause_6,axiom,
    ( c(X1)
    | s(X1,u0r1(X1))
    | r(X1,u0r1(X1))
    | ~ r1most(X1) ) ).

cnf(clause_7,axiom,
    ( c(X1)
    | ~ r1most(X1)
    | ~ r(X1,u0r1(X1))
    | ~ s(X1,u0r1(X1)) ) ).

cnf(clause_8,axiom,
    ( equalish(X3,X2)
    | ~ r1most(X1)
    | ~ r(X1,X3)
    | ~ r(X1,X2) ) ).

cnf(clause_9,axiom,
    ( r1most(X1)
    | ~ equalish(u1r2(X1),u1r1(X1)) ) ).

cnf(clause_10,axiom,
    ( r1most(X1)
    | r(X1,u1r1(X1)) ) ).

cnf(clause_11,axiom,
    ( r1most(X1)
    | r(X1,u1r2(X1)) ) ).

cnf(clause_12,axiom,
    ( ~ d(X1)
    | ~ r(X1,X2)
    | ~ s(X1,X2) ) ).

cnf(clause_13,axiom,
    ( s1most(X1)
    | ~ d(X1) ) ).

cnf(clause_14,axiom,
    ( d(X1)
    | s(X1,u2r1(X1))
    | ~ s1most(X1) ) ).

cnf(clause_15,axiom,
    ( d(X1)
    | r(X1,u2r1(X1))
    | ~ s1most(X1) ) ).

cnf(clause_16,axiom,
    ( equalish(X3,X2)
    | ~ s1most(X1)
    | ~ s(X1,X3)
    | ~ s(X1,X2) ) ).

cnf(clause_17,axiom,
    ( s1most(X1)
    | ~ equalish(u3r2(X1),u3r1(X1)) ) ).

cnf(clause_18,axiom,
    ( s1most(X1)
    | s(X1,u3r1(X1)) ) ).

cnf(clause_19,axiom,
    ( s1most(X1)
    | s(X1,u3r2(X1)) ) ).

%--------------------------------------------------------------------------
