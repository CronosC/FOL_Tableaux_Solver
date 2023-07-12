%--------------------------------------------------------------------------
% File     : SET043-5 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Russell's Paradox
% Version  : [Pel86] axioms : Incomplete.
% English  : Russell's paradox : there is no Russell set (a set which
%            contains exactly those sets which are not members
%            of themselves).

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 39 [Pel86]
%          : p39.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :    2 (   0 unt;   1 nHn;   1 RR)
%            Number of literals    :    4 (   0 equ;   2 neg)
%            Maximal clause size   :    2 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   1 con; 0-0 aty)
%            Number of variables   :    2 (   0 sgn)
% SPC      : CNF_UNS_EPR_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    ( ~ element(X,a)
    | ~ element(X,X) ) ).

cnf(clause_2,negated_conjecture,
    ( element(X,X)
    | element(X,a) ) ).

%--------------------------------------------------------------------------
