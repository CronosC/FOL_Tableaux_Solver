%--------------------------------------------------------------------------
% File     : LCL415-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Logic Calculi (Intuitionistic implication)
% Problem  : Non-axiom for intuitionistic implication
% Version  : [EF+02] axioms.
% English  : Show that the candidate formula is not a single axiom for
%            intuitionistic implication by finding a model in which the
%            required property fails.

% Refs     : [EF+02] Ernst et al. (2002), More First-order Test Problems in
% Source   : [EF+02]
% Names    : intuit-imp [EF+02]

% Status   : Satisfiable
% Rating   : 0.67 v8.1.0, 0.33 v7.5.0, 0.67 v6.2.0, 0.60 v6.1.0, 0.33 v5.5.0, 0.50 v5.4.0, 0.78 v5.3.0, 0.71 v5.0.0, 0.88 v4.1.0, 0.86 v4.0.1, 0.71 v4.0.0, 0.75 v3.5.0, 0.86 v3.4.0, 0.83 v3.3.0, 0.67 v3.2.0, 0.80 v3.1.0, 0.43 v2.7.0, 0.40 v2.6.0, 0.50 v2.5.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-2 aty)
%            Number of variables   :    6 (   1 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
%----Condensed detachment
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(A,B))
    | ~ is_a_theorem(A)
    | is_a_theorem(B) ) ).

%----Candidate
cnf(candidate,axiom,
    is_a_theorem(implies(implies(A,B),implies(implies(B,implies(implies(C,A),D)),implies(A,D)))) ).

%----Required property
cnf(prove_required_property,negated_conjecture,
    ~ is_a_theorem(implies(a,implies(b,a))) ).

%--------------------------------------------------------------------------
