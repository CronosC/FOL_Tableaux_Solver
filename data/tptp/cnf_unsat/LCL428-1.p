%--------------------------------------------------------------------------
% File     : LCL428-1 : TPTP v8.1.2. Bugfixed v5.5.0.
% Domain   : Logic Calculi (Implication in many valued sentential)
% Problem  : Prove the Harris/Rezus axiom from MV1-MV3 and MV5
% Version  : [Var01] axioms.
% English  :

% Refs     : [Ver01] Veroff (2001), A Strategy for Proving Theorems in Many
% Source   : [Ver01]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.57 v8.1.0, 0.50 v6.1.0, 0.64 v6.0.0, 0.56 v5.5.0
% Syntax   : Number of clauses     :    6 (   5 unt;   0 nHn;   2 RR)
%            Number of literals    :    8 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :   13 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :   18 (  18 usr;  17 con; 0-2 aty)
%            Number of variables   :   11 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : MV5 is called MV in other places, e.g., LCL109.
% Bugfixes : v5.5.0 - Fixed prove_hr to use Skolem constants.
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

cnf(mv5,axiom,
    is_a_theorem(implies(implies(implies(X,Y),implies(Y,X)),implies(Y,X))) ).

%----HR
cnf(prove_hr,negated_conjecture,
    ~ is_a_theorem(implies(implies(implies(x,implies(y,x)),implies(implies(implies(implies(implies(implies(implies(implies(implies(z,u),implies(implies(v,z),implies(v,u))),implies(implies(w,implies(v6,w)),v7)),v7),implies(implies(implies(implies(v8,v9),v9),implies(implies(v9,v8),v8)),v10)),v10),implies(implies(implies(implies(v11,v12),implies(v12,v11)),implies(v12,v11)),v13)),v13),implies(implies(v14,implies(v15,v14)),v16))),v16)) ).

%--------------------------------------------------------------------------