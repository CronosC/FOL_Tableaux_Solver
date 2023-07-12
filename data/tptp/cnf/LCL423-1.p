%--------------------------------------------------------------------------
% File     : LCL423-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Logic Calculi (Implication/Negation 2 valued sentential)
% Problem  : Luka-23 is a single axiom
% Version  : [EF+02] axioms.
% English  : Show that the formula Luka-23 is a single axiom for two-valued
%            logic by deriving the Lukasiewicz 3-basis.

% Refs     : [FW01]  Fitelson & Wos (2001), Missing Proofs Found
%          : [EF+02] Ernst et al. (2002), More First-order Test Problems in
% Source   : [EF+02]
% Names    : twoval-luka-23 [EF+02]

% Status   : Unsatisfiable
% Rating   : 0.86 v8.1.0, 0.75 v7.4.0, 0.83 v7.3.0, 0.75 v6.2.0, 0.83 v6.1.0, 1.00 v4.0.1, 0.86 v3.4.0, 0.80 v3.3.0, 0.67 v3.2.0, 0.33 v3.1.0, 1.00 v2.5.0
% Syntax   : Number of clauses     :    3 (   1 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   5 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   3 con; 0-2 aty)
%            Number of variables   :    8 (   3 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
%----Condensed detachment
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(A,B))
    | ~ is_a_theorem(A)
    | is_a_theorem(B) ) ).

%----Luka-23
cnf(luka23,axiom,
    is_a_theorem(implies(implies(implies(A,B),implies(implies(implies(not(C),not(D)),E),C)),implies(F,implies(implies(C,A),implies(D,A))))) ).

%----Denial of Lukasiewicz 3-basis
cnf(prove_luka_3_basis,negated_conjecture,
    ( ~ is_a_theorem(implies(implies(a,b),implies(implies(b,c),implies(a,c))))
    | ~ is_a_theorem(implies(implies(not(a),a),a))
    | ~ is_a_theorem(implies(a,implies(not(a),b))) ) ).

%--------------------------------------------------------------------------
