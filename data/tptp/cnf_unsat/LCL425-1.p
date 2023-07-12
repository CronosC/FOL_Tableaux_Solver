%--------------------------------------------------------------------------
% File     : LCL425-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Logic Calculi (BCI)
% Problem  : BCI+mingle implies Karpenko by condensed detachment
% Version  : [EF+02] axioms.
% English  : Show that if the mingle formula is added to the logic BCI,
%            the Karpenko formula can be derived by condensed detachment.

% Refs     : [EF+02] Ernst et al. (2002), More First-order Test Problems in
%          : [Ern02] Ernst (2002), Completions from TV-> to H->
% Source   : [EF+02]
% Names    : mingle-bci [EF+02]

% Status   : Unsatisfiable
% Rating   : 1.00 v4.0.1, 0.86 v3.4.0, 0.80 v3.3.0, 0.67 v3.1.0, 1.00 v2.5.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-2 aty)
%            Number of variables   :   11 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
%----Condensed detachment
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(A,B))
    | ~ is_a_theorem(A)
    | is_a_theorem(B) ) ).

%----B
cnf(b,axiom,
    is_a_theorem(implies(implies(A,B),implies(implies(C,A),implies(C,B)))) ).

%----C
cnf(c,axiom,
    is_a_theorem(implies(implies(A,implies(B,C)),implies(B,implies(A,C)))) ).

%----Mingle
cnf(mingle,axiom,
    is_a_theorem(implies(implies(implies(implies(implies(A,B),B),A),C),implies(implies(implies(implies(implies(B,A),A),B),C),C))) ).

%----Denial of Karpenko formula
cnf(prove_karpenko,negated_conjecture,
    ~ is_a_theorem(implies(implies(a,implies(implies(b,b),a)),implies(implies(implies(a,b),b),implies(implies(b,a),a)))) ).

%--------------------------------------------------------------------------