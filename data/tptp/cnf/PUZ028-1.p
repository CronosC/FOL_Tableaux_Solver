%--------------------------------------------------------------------------
% File     : PUZ028-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Puzzles
% Problem  : People at a party
% Version  : Especial.
% English  : We can always choose 3 persons who are either familiar with
%            each other or not familiar with each other, from 6 persons
%            who meet at a party.

% Refs     : [ICO92] ICOT (1992), Model Generation Theorem Prover, MGTP
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v7.3.0, 0.25 v7.0.0, 0.00 v2.2.0, 0.33 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   15 (  11 unt;   1 nHn;  15 RR)
%            Number of literals    :   25 (   0 equ;  11 neg)
%            Maximal clause size   :    5 (   1 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 1-2 aty)
%            Number of functors    :    6 (   6 usr;   6 con; 0-0 aty)
%            Number of variables   :   11 (   0 sgn)
% SPC      : CNF_SAT_EPR_NEQ

% Comments : Adapted from [ICO92]
%          : This version is satisfiable because of the argument order in
%            the theorem clauses. We can assume that familiarity is meant
%            symmetrically, but only established in one direction by the
%            after/2 contstraint in familiar_or_not. So really this is
%            wrong, and is corrected in PUZ028-5.
%--------------------------------------------------------------------------
cnf(person1,axiom,
    person(one) ).

cnf(person2,axiom,
    person(two) ).

cnf(person3,axiom,
    person(three) ).

cnf(person4,axiom,
    person(four) ).

cnf(person5,axiom,
    person(five) ).

cnf(person6,axiom,
    person(six) ).

cnf(order1,axiom,
    after(one,two) ).

cnf(order2,axiom,
    after(two,three) ).

cnf(order3,axiom,
    after(three,four) ).

cnf(order4,axiom,
    after(four,five) ).

cnf(order5,axiom,
    after(five,six) ).

cnf(transitivity_of_order,axiom,
    ( after(Large,Small)
    | ~ after(Large,Medium)
    | ~ after(Medium,Small) ) ).

cnf(familiar_or_not,axiom,
    ( familiar(X,Y)
    | not_familiar(X,Y)
    | ~ person(X)
    | ~ person(Y)
    | ~ after(X,Y) ) ).

%----These 3 literals can never all be resolved away because the
%----familiar_or_not axiom prevents X1 > X2 > X3 > X1, as is
%----required by the argument ordering here. That's why it's
%----satisfiable.
cnf(three_familiar,negated_conjecture,
    ( ~ familiar(X1,X2)
    | ~ familiar(X2,X3)
    | ~ familiar(X3,X1) ) ).

cnf(three_not_familiar,negated_conjecture,
    ( ~ not_familiar(X1,X2)
    | ~ not_familiar(X2,X3)
    | ~ not_familiar(X3,X1) ) ).

%--------------------------------------------------------------------------