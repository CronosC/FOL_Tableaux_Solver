%--------------------------------------------------------------------------
% File     : LCL361-1 : TPTP v8.1.2. Released v2.3.0.
% Domain   : Logic Calculi (Implication/Negation 2 valued sentential)
% Problem  : CN-10 depends on the Lukasiewicz system
% Version  : [McC92] axioms.
% English  : An axiomatisation of the Implication/Negation 2 valued
%            sentential calculus is {CN-1,CN-2,CN-3} by Lukasiewicz.
%            Show that CN-10 depends on the Lukasiewicz system.

% Refs     : [Wos96] Wos (1996), Combining Resonance with Heat
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [Wos96]
% Names    : thesis_10 [Wos96]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.08 v5.1.0, 0.06 v5.0.0, 0.07 v4.0.1, 0.00 v2.3.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
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

cnf(prove_cn_10,negated_conjecture,
    ~ is_a_theorem(implies(x,implies(implies(implies(not(x),x),x),implies(implies(y,x),x)))) ).

%--------------------------------------------------------------------------