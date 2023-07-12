%--------------------------------------------------------------------------
% File     : LCL032-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Implication/Falsehood 2 valued sentential)
% Problem  : C0-1 depends on the Merideth axiom
% Version  : [McC92] axioms.
% English  : Axiomatisations for the Implication/Falsehood 2 valued
%            sentential calculus are {C0-1,C0-2,C0-3,C0-4}
%            by Tarski-Bernays, {C0-2,C0-5,C0-6} by Church, and the single
%            Meredith axioms. Show that C0-1 can be derived from the
%            single Meredith axiom.

% Refs     : [Mer53] Meredith (1953), Single Axioms for the Systems (C,N),
%          : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    : C0-44 [MW92]

% Status   : Unsatisfiable
% Rating   : 0.29 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0, 0.00 v7.0.0, 0.25 v6.2.0, 0.50 v6.1.0, 0.86 v6.0.0, 0.78 v5.5.0, 0.88 v5.4.0, 1.00 v5.1.0, 0.94 v5.0.0, 0.93 v4.0.1, 0.57 v3.7.0, 0.71 v3.4.0, 0.60 v3.3.0, 0.00 v3.2.0, 0.33 v3.1.0, 0.50 v2.7.0, 0.88 v2.6.0, 0.86 v2.5.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   4 con; 0-2 aty)
%            Number of variables   :    7 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(c0_CAMerideth,axiom,
    is_a_theorem(implies(implies(implies(implies(implies(X,Y),implies(Z,falsehood)),U),V),implies(implies(V,X),implies(Z,X)))) ).

cnf(prove_c0_1,negated_conjecture,
    ~ is_a_theorem(implies(implies(a,b),implies(implies(b,c),implies(a,c)))) ).

%--------------------------------------------------------------------------
