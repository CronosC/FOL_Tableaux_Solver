%--------------------------------------------------------------------------
% File     : LCL088-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Implicational propositional)
% Problem  : IC-3 depends on the 4th Lukasiewicz axiom
% Version  : [TPTP] axioms.
% English  : Axiomatisations of the Implicational propositional calculus
%            are {IC-2,IC-3,IC-4} by Tarski-Bernays and single Lukasiewicz
%            axioms.Show that IC-3 depends on the fourth Lukasiewicz
%            axiom.

% Refs     : [Luk48] Lukasiewicz (1948), The Shortest Axiom of the Implicat
%          : [Pfe88] Pfenning (1988), Single Axioms in the Implicational Pr
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v6.1.0, 0.07 v6.0.0, 0.00 v5.5.0, 0.12 v5.4.0, 0.17 v5.3.0, 0.20 v5.2.0, 0.08 v5.1.0, 0.19 v5.0.0, 0.20 v4.0.1, 0.00 v2.6.0, 0.29 v2.5.0, 0.00 v2.4.0, 0.00 v2.3.0, 0.14 v2.2.1, 0.33 v2.1.0, 0.38 v2.0.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-2 aty)
%            Number of variables   :    7 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(ic_JLukasiewicz_4,axiom,
    is_a_theorem(implies(implies(implies(P,Q),implies(R,S)),implies(T,implies(implies(S,P),implies(R,P))))) ).

cnf(prove_ic_3,negated_conjecture,
    ~ is_a_theorem(implies(implies(implies(a,b),a),a)) ).

%--------------------------------------------------------------------------
