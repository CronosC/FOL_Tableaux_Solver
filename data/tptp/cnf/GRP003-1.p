%--------------------------------------------------------------------------
% File     : GRP003-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Group Theory
% Problem  : The left identity is also a right identity
% Version  : [Cha70] axioms : Incomplete.
% English  :

% Refs     : [Luc68] Luckham (1968), Some Tree-paring Strategies for Theore
%          : [Cha70] Chang (1970), The Unit Proof and the Input Proof in Th
%          : [CL73]  Chang & Lee (1973), Symbolic Logic and Mechanical Theo
% Source   : [Cha70]
% Names    : Example 2 [Luc68]
%          : Example 3 [Cha70]
%          : Example 3 [CL73]
%          : EX3 [SPRFN]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    5 (   3 unt;   0 nHn;   3 RR)
%            Number of literals    :   11 (   0 equ;   7 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-1 aty)
%            Number of variables   :   14 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(left_inverse,axiom,
    product(inverse(X),X,identity) ).

cnf(left_identity,axiom,
    product(identity,X,X) ).

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

cnf(prove_there_is_a_right_identity,negated_conjecture,
    ~ product(a,identity,a) ).

%--------------------------------------------------------------------------
