%--------------------------------------------------------------------------
% File     : GEO079-1 : TPTP v8.1.2. Released v1.1.0.
% Domain   : Geometry
% Problem  : The alternate interior angles in a trapezoid are equal
% Version  : [Cha70] axioms : Incomplete.
% English  : The alternate interior angles formed by a diagonal of a (not
%            necessarily isosceles) trapezoid are equal.

% Refs     : [Sla67] Slagle (1967), Automatic Theorem Proving with Renamabl
% Source   : [Sla67]
% Names    : GEOMETRY THEOREM [Sla67]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :    6 (   2 unt;   0 nHn;   6 RR)
%            Number of literals    :   11 (   0 equ;   6 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    5 (   5 usr;   0 prp; 3-6 aty)
%            Number of functors    :    4 (   4 usr;   4 con; 0-0 aty)
%            Number of variables   :   20 (   0 sgn)
% SPC      : CNF_UNS_EPR_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(right_angles_are_equal,axiom,
    ( ~ right_angle(U,V,W)
    | ~ right_angle(X,Y,Z)
    | eq(U,V,W,X,Y,Z) ) ).

cnf(corresponding_angles_are_equal,axiom,
    ( ~ congruent(U,V,W,X,Y,Z)
    | eq(U,V,W,X,Y,Z) ) ).

cnf(trapezoid_definition,axiom,
    ( ~ trapezoid(U,V,W,X)
    | parallel(V,W,U,X) ) ).

cnf(interior_angles_are_equal,axiom,
    ( ~ parallel(U,V,X,Y)
    | eq(X,V,U,V,X,Y) ) ).

cnf(a_trapezoid,hypothesis,
    trapezoid(a,b,c,d) ).

cnf(prove_angles_equal,negated_conjecture,
    ~ eq(a,c,b,c,a,d) ).

%--------------------------------------------------------------------------
