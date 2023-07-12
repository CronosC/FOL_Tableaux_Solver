%--------------------------------------------------------------------------
% File     : KRS004-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Knowledge Representation
% Problem  : Paramasivam problem T-Box 1d
% Version  : Especial.
% English  : c exists.

% Refs     : [PP95]  Paramasivam & Plaisted (1995), Automated Deduction Tec
% Source   : [PP95]
% Names    : Problem 1(d) [PP95]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.1.0
% Syntax   : Number of clauses     :    4 (   1 unt;   0 nHn;   4 RR)
%            Number of literals    :    7 (   0 equ;   5 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 1-1 aty)
%            Number of functors    :    1 (   1 usr;   1 con; 0-0 aty)
%            Number of variables   :    3 (   0 sgn)
% SPC      : CNF_UNS_EPR_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    c(exist) ).

cnf(clause_2,axiom,
    ( d(X1)
    | ~ c(X1) ) ).

cnf(clause_3,axiom,
    ( ~ c(X1)
    | ~ d(X1) ) ).

cnf(clause_4,axiom,
    ( ~ d(X1)
    | ~ c(X1) ) ).

%--------------------------------------------------------------------------
