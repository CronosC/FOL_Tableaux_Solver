%--------------------------------------------------------------------------
% File     : LCL064-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Implication/Negation 2 valued sentential)
% Problem  : CN-1 depends on the Church system
% Version  : [McC92] axioms.
% English  : Axiomatisations of the Implication/Negation 2 valued
%            sentential calculus are {CN-1,CN-2,CN-3} by Lukasiewicz,
%            {CN-18,CN-21,CN-35,CN-39,CN-39,CN-40,CN-46} by Frege,
%            {CN-3,CN-18,CN-21,CN-22,CN-30,CN-54} by Hilbert, {CN-18,
%            CN-35,CN-49} by Church, {CN-19,CN-37,CN-59} by Lukasiewicz,
%            {CN-19,CN-37,CN-60} by Wos, and the single Meredith axiom.
%            Show that CN-X depends on the Church system.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    : CN-25 [MW92]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.4.0, 0.17 v7.3.0, 0.00 v6.1.0, 0.36 v6.0.0, 0.22 v5.5.0, 0.19 v5.4.0, 0.33 v5.3.0, 0.45 v5.2.0, 0.38 v5.1.0, 0.31 v5.0.0, 0.33 v4.0.1, 0.00 v2.7.0, 0.25 v2.6.0, 0.14 v2.4.0, 0.14 v2.3.0, 0.43 v2.2.1, 0.22 v2.1.0, 0.25 v2.0.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   3 con; 0-2 aty)
%            Number of variables   :    9 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

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

cnf(cn_49,axiom,
    is_a_theorem(implies(implies(not(X),not(Y)),implies(Y,X))) ).

cnf(prove_cn_1,negated_conjecture,
    ~ is_a_theorem(implies(implies(a,b),implies(implies(b,c),implies(a,c)))) ).

%--------------------------------------------------------------------------
