%--------------------------------------------------------------------------
% File     : LCL063-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Implication/Negation 2 valued sentential)
% Problem  : CN-CAMerideth depends on the Lukasiewicz system
% Version  : [McC92] axioms.
% English  : Axiomatisations of the Implication/Negation 2 valued
%            sentential calculus are {CN-1,CN-2,CN-3} by Lukasiewicz,
%            {CN-18,CN-21,CN-35,CN-39,CN-39,CN-40,CN-46} by Frege,
%            {CN-3,CN-18,CN-21,CN-22,CN-30,CN-54} by Hilbert, {CN-18,
%            CN-35,CN-49} by Church, {CN-19,CN-37,CN-59} by Lukasiewicz,
%            {CN-19,CN-37,CN-60} by Wos, and the single Meredith axiom.
%            Show that the single Meredith axiom depends on the short
%            Lukasiewicz system.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    : CN-24 [MW92]

% Status   : Unsatisfiable
% Rating   : 1.00 v8.1.0, 0.75 v7.4.0, 0.67 v7.3.0, 0.75 v6.2.0, 0.83 v6.1.0, 0.93 v6.0.0, 0.89 v5.5.0, 0.94 v5.3.0, 0.95 v5.2.0, 1.00 v4.0.0, 0.86 v3.4.0, 0.80 v3.3.0, 0.33 v3.2.0, 0.67 v3.1.0, 0.83 v2.7.0, 1.00 v2.6.0, 0.86 v2.5.0, 1.00 v2.4.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    7 (   7 usr;   5 con; 0-2 aty)
%            Number of variables   :    8 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(cn_1,axiom,
    is_a_theorem(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z)))) ).

cnf(cn_2,axiom,
    is_a_theorem(implies(implies(not(X),X),X)) ).

cnf(cn_3,axiom,
    is_a_theorem(implies(X,implies(not(X),Y))) ).

cnf(prove_cn_CAMerideth,negated_conjecture,
    ~ is_a_theorem(implies(implies(implies(implies(implies(a,b),implies(not(c),not(e))),c),falsehood),implies(implies(falsehood,a),implies(e,a)))) ).

%--------------------------------------------------------------------------
