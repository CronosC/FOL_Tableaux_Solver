%--------------------------------------------------------------------------
% File     : LCL078-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Implication/Negation 2 valued sentential)
% Problem  : CN-40 depends on CN-18 CN-35 CN-46
% Version  : [Pel86] axioms.
% English  : Axiomatisations of the Implication/Negation 2 valued
%            sentential calculus are {CN-1,CN-2,CN-3} by Lukasiewicz,
%            {CN-18,CN-21,CN-35,CN-39,CN-39,CN-40,CN-46} by Frege,
%            {CN-3,CN-18,CN-21,CN-22,CN-30,CN-54} by Hilbert, {CN-18,
%            CN-35,CN-49} by Church, {CN-19,CN-37,CN-59} by Lukasiewicz,
%            {CN-19,CN-37,CN-60} by Wos, and the single Meredith axiom.
%            Show that CN-40 depends on the modified Church system
%            {CN-18,CN-35,CN-46}.

% Refs     : [Mor84] Morgan (1984), Logic Problems
%          : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 68 [Pel86]
%          : morgan.five.ver2.in [ANL]

% Status   : Satisfiable
% Rating   : 0.00 v8.1.0, 0.33 v7.5.0, 0.00 v6.2.0, 0.20 v6.1.0, 0.00 v5.5.0, 0.25 v5.4.0, 0.89 v5.3.0, 0.86 v5.0.0, 0.62 v4.1.0, 0.57 v4.0.0, 0.62 v3.5.0, 0.71 v3.4.0, 0.83 v3.2.0, 0.80 v3.1.0, 0.86 v2.7.0, 0.80 v2.6.0, 0.75 v2.5.0, 0.50 v2.4.0, 0.67 v2.2.1, 0.75 v2.2.0, 0.67 v2.1.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :    9 (   1 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(cn_18,axiom,
    is_a_theorem(implies(X,implies(Y,X))) ).

cnf(cn_35,axiom,
    is_a_theorem(implies(implies(X,implies(Y,Z)),implies(implies(X,Y),implies(X,Z)))) ).

cnf(cn_46,axiom,
    is_a_theorem(implies(implies(Y,X),implies(not(X),not(Y)))) ).

cnf(prove_cn_40,negated_conjecture,
    ~ is_a_theorem(implies(a,not(not(a)))) ).

%--------------------------------------------------------------------------
