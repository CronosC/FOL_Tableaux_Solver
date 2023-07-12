%--------------------------------------------------------------------------
% File     : LCL167-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Equivalential)
% Problem  : YRO depends on XHK
% Version  : [WW+90] axioms.
% English  : Show that the single Meredith axiom YRO can be derived from
%            the single Winker axiom XHK.

% Refs     : [WW+90] Wos et al. (1990), Automated Reasoning Contributes to
%          : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
% Source   : [WW+90]
% Names    : EC-2 [WW+90]

% Status   : Unsatisfiable
% Rating   : 0.43 v8.1.0, 0.25 v7.4.0, 0.33 v7.3.0, 0.25 v6.2.0, 0.50 v6.1.0, 0.71 v6.0.0, 0.56 v5.5.0, 0.81 v5.4.0, 0.83 v5.3.0, 0.90 v5.2.0, 0.77 v5.1.0, 0.81 v5.0.0, 0.80 v4.0.1, 0.57 v3.4.0, 0.40 v3.3.0, 0.33 v3.1.0, 0.50 v2.6.0, 0.57 v2.5.0, 0.71 v2.4.0, 0.71 v2.3.0, 0.71 v2.2.1, 0.89 v2.2.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   3 con; 0-2 aty)
%            Number of variables   :    5 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(equivalent(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

%----Axiom by Winker
cnf(xhk,axiom,
    is_a_theorem(equivalent(X,equivalent(equivalent(Y,Z),equivalent(equivalent(X,Z),Y)))) ).

%----Axiom by Meredith
cnf(prove_yro,negated_conjecture,
    ~ is_a_theorem(equivalent(equivalent(a,b),equivalent(c,equivalent(equivalent(c,b),a)))) ).

%--------------------------------------------------------------------------
