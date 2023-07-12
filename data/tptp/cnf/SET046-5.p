%--------------------------------------------------------------------------
% File     : SET046-5 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Set Theory
% Problem  : No set of non-circular sets
% Version  : [Pel86] axioms : Incomplete.
% English  : A set is circular if it is a member of another set which
%            in turn is a member of the orginal. Intuitively all sets are
%            non-circular. Prove there is no set of non-circular sets.

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 42 [Pel86]
%          : p42.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.4.0, 0.17 v7.1.0, 0.33 v7.0.0, 0.25 v6.3.0, 0.29 v6.2.0, 0.11 v6.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    3 (   0 unt;   2 nHn;   1 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   1 con; 0-1 aty)
%            Number of variables   :    4 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    ( ~ element(X,a)
    | ~ element(X,Y)
    | ~ element(Y,X) ) ).

cnf(clause_2,negated_conjecture,
    ( element(X,f(X))
    | element(X,a) ) ).

cnf(clause_3,negated_conjecture,
    ( element(f(X),X)
    | element(X,a) ) ).

%--------------------------------------------------------------------------
