%--------------------------------------------------------------------------
% File     : GRP005-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Group Theory
% Problem  : Identity is in this subset of a group
% Version  : [Cha70] axioms : Incomplete.
% English  : If S is a non-empty subset of a group such that
%            if X, Y belong to S, the XY^-1 belongs to S, then the
%            identity e belongs to S.

% Refs     : [Luc68] Luckham (1968), Some Tree-paring Strategies for Theore
%          : [Cha70] Chang (1970), The Unit Proof and the Input Proof in Th
%          : [CL73]  Chang & Lee (1973), Symbolic Logic and Mechanical Theo
% Source   : [Cha70]
% Names    : Example 5 [Luc68]
%          : Example 5 [Cha70]
%          : Example 5 [CL73]
%          : EX5 [SPRFN]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    9 (   6 unt;   0 nHn;   5 RR)
%            Number of literals    :   18 (   0 equ;  10 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 1-3 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-1 aty)
%            Number of variables   :   19 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(left_identity,axiom,
    product(identity,X,X) ).

cnf(right_identity,axiom,
    product(X,identity,X) ).

cnf(right_inverse,axiom,
    product(X,inverse(X),identity) ).

cnf(left_inverse,axiom,
    product(inverse(X),X,identity) ).

cnf(element_of_set,axiom,
    an_element(a) ).

cnf(condition,axiom,
    ( ~ an_element(X)
    | ~ an_element(Y)
    | ~ product(X,inverse(Y),Z)
    | an_element(Z) ) ).

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

cnf(prove_identity_is_an_element,negated_conjecture,
    ~ an_element(identity) ).

%--------------------------------------------------------------------------
