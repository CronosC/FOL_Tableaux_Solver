%--------------------------------------------------------------------------
% File     : LCL072-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Implication/Negation 2 valued sentential)
% Problem  : CN-3 depends on the Wos system
% Version  : [McC92] axioms.
% English  : Axiomatisations of the Implication/Negation 2 valued
%            sentential calculus are {CN-1,CN-2,CN-3} by Lukasiewicz,
%            {CN-18,CN-21,CN-35,CN-39,CN-39,CN-40,CN-46} by Frege,
%            {CN-3,CN-18,CN-21,CN-22,CN-30,CN-54} by Hilbert, {CN-18,
%            CN-35,CN-49} by Church, {CN-19,CN-37,CN-59} by Lukasiewicz,
%            {CN-19,CN-37,CN-60} by Wos, and the single Meredith axiom.
%            Show that CN-3 depends on the Wos system.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    : CN-33 [MW92]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.15 v5.2.0, 0.08 v5.1.0, 0.06 v5.0.0, 0.07 v4.0.1, 0.00 v3.1.0, 0.17 v2.7.0, 0.12 v2.6.0, 0.00 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :   12 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(cn_19,axiom,
    is_a_theorem(implies(implies(implies(X,Y),Z),implies(Y,Z))) ).

cnf(cn_37,axiom,
    is_a_theorem(implies(implies(implies(X,Y),Z),implies(not(X),Z))) ).

cnf(cn_60,axiom,
    is_a_theorem(implies(implies(X,implies(not(Y),Z)),implies(X,implies(implies(U,Z),implies(implies(Y,U),Z))))) ).

cnf(prove_cn_3,negated_conjecture,
    ~ is_a_theorem(implies(a,implies(not(a),b))) ).

%--------------------------------------------------------------------------
