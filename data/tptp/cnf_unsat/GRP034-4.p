%--------------------------------------------------------------------------
% File     : GRP034-4 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Group Theory (Subgroups)
% Problem  : In subgroups, inverse is closed
% Version  : [LS74] axioms : Incomplete.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental tests of resol
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : ls26 [LS74]
%          : ls26 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    9 (   6 unt;   0 nHn;   5 RR)
%            Number of literals    :   18 (   0 equ;  10 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 1-3 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :   20 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(closure,axiom,
    product(X,Y,multiply(X,Y)) ).

cnf(left_identity,axiom,
    product(identity,X,X) ).

cnf(right_identity,axiom,
    product(X,identity,X) ).

cnf(right_inverse,axiom,
    product(X,inverse(X),identity) ).

cnf(associativity1,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(U,Z,W)
    | product(X,V,W) ) ).

cnf(associativity2,axiom,
    ( ~ product(X,Y,U)
    | ~ product(Y,Z,V)
    | ~ product(X,V,W)
    | product(U,Z,W) ) ).

cnf(closure_of_subgroup,axiom,
    ( ~ subgroup_member(A)
    | ~ subgroup_member(B)
    | ~ product(B,inverse(A),C)
    | subgroup_member(C) ) ).

cnf(a_is_in_subgroup,hypothesis,
    subgroup_member(a) ).

cnf(prove_inverse_is_in_subgroup,negated_conjecture,
    ~ subgroup_member(inverse(a)) ).

%--------------------------------------------------------------------------
