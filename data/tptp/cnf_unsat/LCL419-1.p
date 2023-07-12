%--------------------------------------------------------------------------
% File     : LCL419-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Logic Calculi (Many valued sentential)
% Problem  : Prove AK1 from MV1--MV4
% Version  : [EF+02] axioms.
% English  :

% Refs     : [FH01]  Fitelson and Harris (2001), Distributivity in LN0 and
%          : [Ver01] Veroff (2001), A Strategy for Proving Theorems in Many
%          : [EF+02] Ernst et al. (2002), More First-order Test Problems in
% Source   : [EF+02]
% Names    : mv-dist-star [EF+02]

% Status   : Unsatisfiable
% Rating   : 1.00 v6.2.0, 0.83 v6.1.0, 0.93 v6.0.0, 0.89 v5.5.0, 1.00 v2.5.0
% Syntax   : Number of clauses     :    6 (   5 unt;   0 nHn;   2 RR)
%            Number of literals    :    8 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    8 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   3 con; 0-2 aty)
%            Number of variables   :   11 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
%----Condensed detachment
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(A,B))
    | ~ is_a_theorem(A)
    | is_a_theorem(B) ) ).

cnf(mv1,axiom,
    is_a_theorem(implies(A,implies(B,A))) ).

cnf(mv2,axiom,
    is_a_theorem(implies(implies(A,B),implies(implies(B,C),implies(A,C)))) ).

cnf(mv3,axiom,
    is_a_theorem(implies(implies(implies(A,B),B),implies(implies(B,A),A))) ).

cnf(mv4,axiom,
    is_a_theorem(implies(implies(not(A),not(B)),implies(B,A))) ).

%----AK1
cnf(prove_ak1,negated_conjecture,
    ~ is_a_theorem(implies(implies(implies(a,not(implies(implies(not(b),not(c)),not(c)))),not(implies(implies(not(b),not(c)),not(c)))),not(implies(implies(not(implies(implies(a,b),b)),not(implies(implies(a,c),c))),not(implies(implies(a,c),c)))))) ).

%--------------------------------------------------------------------------
