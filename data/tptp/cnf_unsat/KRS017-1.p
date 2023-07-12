%--------------------------------------------------------------------------
% File     : KRS017-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 7a
% Version  : Especial.
% English  : a subsumes e.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 7(a) [PP95]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.3.0, 0.14 v6.2.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :    7 (   2 unt;   2 nHn;   7 RR)
%            Number of literals    :   17 (   0 equ;   9 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 1-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-1 aty)
%            Number of variables   :   10 (   3 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    e(exists) ).

cnf(clause_2,negated_conjecture,
    ~ a(exists) ).

cnf(clause_3,axiom,
    ( r(X1,u0r3(X1))
    | ~ e(X1) ) ).

cnf(clause_4,axiom,
    ( a(X3)
    | ~ e(X1)
    | ~ r(X1,X2)
    | ~ r(X3,X2) ) ).

cnf(clause_5,axiom,
    ( e(X1)
    | ~ a(u0r2(X1))
    | ~ r(X1,X4) ) ).

cnf(clause_6,axiom,
    ( e(X1)
    | r(u0r2(X1),u0r1(X1))
    | ~ r(X1,X4) ) ).

cnf(clause_7,axiom,
    ( e(X1)
    | r(X1,u0r1(X1))
    | ~ r(X1,X4) ) ).

%--------------------------------------------------------------------------
