%--------------------------------------------------------------------------
% File     : LCL030-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Implication/Falsehood 2 valued sentential)
% Problem  : C0-6 depends on the Tarski-Bernays system
% Version  : [McC92] axioms.
% English  : Axiomatisations for the Implication/Falsehood 2 valued
%            sentential calculus are {C0-1,C0-2,C0-3,C0-4}
%            by Tarski-Bernays, {C0-2,C0-5,C0-6} by Church, and the single
%            Meredith axioms. Show that C0-6 can be derived from the
%            Tarski-Bernays system.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    : C0-42 [MW92]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v6.2.0, 0.33 v6.1.0, 0.50 v6.0.0, 0.33 v5.5.0, 0.75 v5.4.0, 0.72 v5.3.0, 0.75 v5.2.0, 0.54 v5.1.0, 0.56 v5.0.0, 0.47 v4.1.0, 0.40 v4.0.1, 0.14 v3.4.0, 0.20 v3.3.0, 0.00 v3.1.0, 0.17 v2.7.0, 0.75 v2.6.0, 0.57 v2.5.0, 0.14 v2.4.0, 0.43 v2.3.0, 0.71 v2.2.1, 0.89 v2.1.0, 0.88 v2.0.0
% Syntax   : Number of clauses     :    6 (   5 unt;   0 nHn;   2 RR)
%            Number of literals    :    8 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   4 con; 0-2 aty)
%            Number of variables   :   10 (   3 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(c0_1,axiom,
    is_a_theorem(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z)))) ).

cnf(c0_2,axiom,
    is_a_theorem(implies(X,implies(Y,X))) ).

cnf(c0_3,axiom,
    is_a_theorem(implies(implies(implies(X,Y),X),X)) ).

cnf(c0_4,axiom,
    is_a_theorem(implies(falsehood,X)) ).

cnf(prove_c0_6,negated_conjecture,
    ~ is_a_theorem(implies(implies(a,implies(b,c)),implies(implies(a,b),implies(a,c)))) ).

%--------------------------------------------------------------------------