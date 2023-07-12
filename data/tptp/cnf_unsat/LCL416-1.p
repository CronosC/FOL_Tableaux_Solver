%--------------------------------------------------------------------------
% File     : LCL416-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Logic Calculi (Equivalential)
% Problem  : Prove reflexivity from formula XCB by condensed detachment
% Version  : [EF+02] axioms.
% English  :

% Refs     : [WW+83] Wos et al. (1983), Questions Concerning Possible Short
%          : [EF+02] Ernst et al. (2002), More First-order Test Problems in
% Source   : [EF+02]
% Names    : xcb-reflex [EF+02]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.1.0, 0.29 v6.0.0, 0.11 v5.5.0, 0.25 v5.4.0, 0.28 v5.3.0, 0.30 v5.2.0, 0.23 v5.1.0, 0.25 v5.0.0, 0.20 v4.1.0, 0.27 v4.0.1, 0.00 v3.1.0, 0.17 v2.7.0, 0.25 v2.6.0, 0.33 v2.5.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    2 (   2 usr;   1 con; 0-2 aty)
%            Number of variables   :    5 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : This was long thought to be a nontheorem and was first proved
%            by Fitelson.
%--------------------------------------------------------------------------
%----Condensed detachment
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(equivalent(A,B))
    | ~ is_a_theorem(A)
    | is_a_theorem(B) ) ).

%----XCB
cnf(xcb,axiom,
    is_a_theorem(equivalent(A,equivalent(equivalent(equivalent(A,B),equivalent(C,B)),C))) ).

%----Denial of reflexivity
cnf(prove_reflexivity,negated_conjecture,
    ~ is_a_theorem(equivalent(a,a)) ).

%--------------------------------------------------------------------------
