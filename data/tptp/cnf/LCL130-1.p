%--------------------------------------------------------------------------
% File     : LCL130-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Right group)
% Problem  : LG-2 depends on P-4
% Version  : [McC92b] axioms.
% English  : Kalman's axiomatisation of the right group calculus
%            is {LG-1,LG-2,LG-3,LG-4,LG-5}. McCune has shown that LG-2
%            is a single axiom. Other axiomatisations by McCune are
%            {Q-2,Q-3}, {Q-3,Q-4}, S-2, S-3, S-4, P-4, S-6. Show that LG-2
%            depends on P-4.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92a] McCune (1992), Automated Discovery of New Axiomatisat
%          : [McC92b] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92b]
% Names    : RG-111 [MW92]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.2.0, 0.17 v6.1.0, 0.14 v6.0.0, 0.00 v5.5.0, 0.19 v5.4.0, 0.22 v5.3.0, 0.25 v5.2.0, 0.31 v5.1.0, 0.25 v5.0.0, 0.20 v4.0.1, 0.00 v2.7.0, 0.12 v2.6.0, 0.00 v2.4.0, 0.14 v2.3.0, 0.14 v2.2.1, 0.11 v2.2.0, 0.22 v2.1.0, 0.13 v2.0.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   4 con; 0-2 aty)
%            Number of variables   :    6 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(equivalent(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(p_4,axiom,
    is_a_theorem(equivalent(equivalent(X,equivalent(equivalent(Y,Z),equivalent(equivalent(Y,U),equivalent(Z,U)))),X)) ).

cnf(prove_lg_2,negated_conjecture,
    ~ is_a_theorem(equivalent(a,equivalent(a,equivalent(equivalent(b,c),equivalent(equivalent(b,e),equivalent(c,e)))))) ).

%--------------------------------------------------------------------------
