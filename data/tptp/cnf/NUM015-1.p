%--------------------------------------------------------------------------
% File     : NUM015-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Number Theory
% Problem  : Any number greater than 1 has a prime divisor
% Version  : [Cha70] axioms : Incomplete.
% English  :

% Refs     : [Luc68] Luckham (1968), Some Tree-paring Strategies for Theore
%          : [Lov69] Loveland (1969), Theorem-provers Combining Model Elimi
%          : [Cha70] Chang (1970), The Unit Proof and the Input Proof in Th
%          : [RR+72] Reboh et al. (1972), Study of automatic theorem provin
%          : [CL73]  Chang & Lee (1973), Symbolic Logic and Mechanical Theo
%          : [FL+74] Fleisig et al. (1974), An Implementation of the Model
% Source   : [Cha70]
% Names    : Example 7 [Luc68]
%          : Example 2 [Lov69]
%          : Example 8 [Cha70]
%          : Example 8 [Cl73]
%          : PRIM [RR+72]
%          : Example 3 [FL+74]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.3.0, 0.14 v6.2.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    9 (   2 unt;   3 nHn;   5 RR)
%            Number of literals    :   19 (   0 equ;   8 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 1-2 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-1 aty)
%            Number of variables   :   10 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(divide_self,axiom,
    divides(X,X) ).

cnf(transitive_divide,axiom,
    ( ~ divides(X,Y)
    | ~ divides(Y,Z)
    | divides(X,Z) ) ).

cnf(prime,axiom,
    ( prime(X)
    | divides(divisor(X),X) ) ).

cnf(divisor1,axiom,
    ( prime(X)
    | less(n1,divisor(X)) ) ).

cnf(divisor2,axiom,
    ( prime(X)
    | less(divisor(X),X) ) ).

cnf(factor1,axiom,
    ( ~ less(n1,X)
    | ~ less(X,a)
    | prime(factor_of(X)) ) ).

cnf(factor2,axiom,
    ( ~ less(n1,X)
    | ~ less(X,a)
    | divides(factor_of(X),X) ) ).

cnf(a_is_greater_than_1,hypothesis,
    less(n1,a) ).

cnf(prove_a_has_prime_divisor,negated_conjecture,
    ( ~ prime(X)
    | ~ divides(X,a) ) ).

%--------------------------------------------------------------------------
