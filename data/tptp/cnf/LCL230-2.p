%--------------------------------------------------------------------------
% File     : LCL230-2 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Propositional)
% Problem  : Principia Mathematica 2.85
% Version  : [Pel86] axioms.
% English  : Judged by [SRM73] to be the 'hardest' of the first 67 theorems
%            of [WR27].

% Refs     : [WR27]  Whitehead & Russell (1927), Principia Mathematica
%          : [SRM73] Siklossy et al. (1973), Breadth First Search: Some Sur
%          : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 5 [Pel86]

% Status   : Unsatisfiable
% Rating   : 0.00 v4.1.0, 0.20 v3.7.0, 0.25 v3.5.0, 0.00 v3.3.0, 0.33 v3.2.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    4 (   3 unt;   1 nHn;   4 RR)
%            Number of literals    :    6 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :    3 (   3 usr;   3 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0 sgn)
% SPC      : CNF_UNS_PRP

% Comments :
% Bugfixes : v1.1.1 - Renamed from SYN043-1.
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    ( ~ q
    | p
    | r ) ).

cnf(clause_2,negated_conjecture,
    ~ p ).

cnf(clause_3,negated_conjecture,
    q ).

cnf(clause_4,negated_conjecture,
    ~ r ).

%--------------------------------------------------------------------------
