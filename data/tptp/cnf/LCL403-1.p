%--------------------------------------------------------------------------
% File     : LCL403-1 : TPTP v8.1.2. Released v2.3.0.
% Domain   : Logic Calculi (Implication/Negation 2 valued sentential)
% Problem  : CN-69 depends on the Lukasiewicz system
% Version  : [McC92] axioms.
% English  : An axiomatisation of the Implication/Negation 2 valued
%            sentential calculus is {CN-1,CN-2,CN-3} by Lukasiewicz.
%            Show that CN-69 depends on the Lukasiewicz system.

% Refs     : [Wos96] Wos (1996), Combining Resonance with Heat
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [Wos96]
% Names    : thesis_69 [Wos96]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0, 0.00 v6.2.0, 0.33 v6.1.0, 0.57 v6.0.0, 0.44 v5.5.0, 0.56 v5.4.0, 0.61 v5.3.0, 0.70 v5.2.0, 0.46 v5.1.0, 0.56 v5.0.0, 0.53 v4.0.1, 0.14 v3.4.0, 0.20 v3.3.0, 0.33 v3.2.0, 0.00 v3.1.0, 0.33 v2.7.0, 0.62 v2.6.0, 0.57 v2.5.0, 0.43 v2.4.0, 0.25 v2.3.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
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

cnf(prove_cn_69,negated_conjecture,
    ~ is_a_theorem(implies(x,implies(not(y),not(implies(x,y))))) ).

%--------------------------------------------------------------------------
