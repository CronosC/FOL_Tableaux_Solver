%--------------------------------------------------------------------------
% File     : NUM016-2 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Number Theory
% Problem  : There exist infinitely many primes
% Version  : [Cha70] axioms : Incomplete.
% English  :

% Refs     : [Luc68] Luckham (1968), Some Tree-paring Strategies for Theore
%          : [Cha70] Chang (1970), The Unit Proof and the Input Proof in Th
%          : [CL73]  Chang & Lee (1973), Symbolic Logic and Mechanical Theo
% Source   : [Cha70]
% Names    : Example 8a [Luc68]
%          : Example 9 [Cha70]
%          : Example 9 [CL73]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.3.0, 0.14 v6.2.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    8 (   2 unt;   3 nHn;   4 RR)
%            Number of literals    :   15 (   0 equ;   6 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 1-2 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-1 aty)
%            Number of variables   :   10 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(nothing_is_less_than_itself,axiom,
    ~ less(X,X) ).

cnf(numbers_are_different,axiom,
    ( ~ less(X,Y)
    | ~ less(Y,X) ) ).

cnf(a_prime_is_less_than_the_next_one,axiom,
    less(X,factorial_plus_one(X)) ).

cnf(divisor_is_smaller,axiom,
    ( ~ divides(X,factorial_plus_one(Y))
    | less(Y,X) ) ).

cnf(division_by_prime_divisor,axiom,
    ( prime(X)
    | divides(prime_divisor(X),X) ) ).

cnf(prime_divsiors,axiom,
    ( prime(X)
    | prime(prime_divisor(X)) ) ).

cnf(smaller_prime_divisors,axiom,
    ( prime(X)
    | less(prime_divisor(X),X) ) ).

cnf(prove_there_is_another_prime,negated_conjecture,
    ( ~ prime(X)
    | ~ less(a,X)
    | less(factorial_plus_one(a),X) ) ).

%--------------------------------------------------------------------------
