%--------------------------------------------------------------------------
% File     : LCL424-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Logic Calculi (Implication/Negation 2 valued sentential)
% Problem  : Mer-21 is a single axiom for two-valued logic
% Version  : [EF+02] axioms.
% English  : Show that the formula Mer-21 is a single axiom for two-valued
%            logic by deriving the Lukasiewicz 3-basis.

% Refs     : [Wos01] Wos (2001), Conquering the Meredith Single Axiom
%          : [EF+02] Ernst et al. (2002), More First-order Test Problems in
% Source   : [EF+02]
% Names    : twoval-mer-21 [EF+02]

% Status   : Unsatisfiable
% Rating   : 1.00 v2.5.0
% Syntax   : Number of clauses     :    3 (   1 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   5 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   3 con; 0-2 aty)
%            Number of variables   :    7 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
%----Condensed detachment
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(A,B))
    | ~ is_a_theorem(A)
    | is_a_theorem(B) ) ).

%----Mer-21
cnf(mer21,axiom,
    is_a_theorem(implies(implies(implies(implies(implies(A,B),implies(not(C),not(D))),C),E),implies(implies(E,A),implies(D,A)))) ).

%----Denial of Lukasiewicz 3-basis
cnf(prove_luka_3_basis,negated_conjecture,
    ( ~ is_a_theorem(implies(implies(a,b),implies(implies(b,c),implies(a,c))))
    | ~ is_a_theorem(implies(implies(not(a),a),a))
    | ~ is_a_theorem(implies(a,implies(not(a),b))) ) ).

%--------------------------------------------------------------------------
