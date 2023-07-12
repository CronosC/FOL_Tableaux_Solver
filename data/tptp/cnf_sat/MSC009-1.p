%--------------------------------------------------------------------------
% File     : MSC009-1 : TPTP v8.1.2. Released v1.2.0.
% Domain   : Miscellaneous
% Problem  : Definitions of a family structure
% Version  : Especial.
% English  :

% Refs     : [FL+93] Fermuller et al. (1993), Resolution Methods for the De
% Source   : [FL+93]
% Names    : KL-ONE-example [FL+93]

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0, 0.17 v2.4.0, 0.00 v2.2.0, 0.33 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   28 (   0 unt;   4 nHn;  27 RR)
%            Number of literals    :   70 (   0 equ;  40 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   11 (  11 usr;   0 prp; 1-2 aty)
%            Number of functors    :    6 (   6 usr;   0 con; 1-1 aty)
%            Number of variables   :   35 (   0 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
cnf(female1,negated_conjecture,
    ( ~ female(X)
    | ~ male(X) ) ).

cnf(female2,negated_conjecture,
    ( male(X)
    | female(X) ) ).

cnf(person1,negated_conjecture,
    ( ~ person(X)
    | sex(X,sex_of1(X)) ) ).

cnf(person2,negated_conjecture,
    ( ~ person(X)
    | male(sex_of1(X))
    | female(sex_of1(X)) ) ).

cnf(person3,negated_conjecture,
    ( ~ sex(X,Y)
    | ~ male(Y)
    | person(X) ) ).

cnf(person4,negated_conjecture,
    ( ~ sex(X,Y)
    | ~ female(Y)
    | person(X) ) ).

cnf(parent1,negated_conjecture,
    ( ~ parent(X)
    | person(X) ) ).

cnf(parent2,negated_conjecture,
    ( ~ parent(X)
    | child(X,child_of1(X)) ) ).

cnf(parent3,negated_conjecture,
    ( ~ parent(X)
    | person(child_of1(X)) ) ).

cnf(parent4,negated_conjecture,
    ( ~ person(X)
    | ~ child(X,Y)
    | ~ person(Y)
    | parent(X) ) ).

cnf(mother1,negated_conjecture,
    ( ~ mother(X)
    | parent(X) ) ).

cnf(mother2,negated_conjecture,
    ( ~ mother(X)
    | sex(X,sex_of2(X)) ) ).

cnf(mother3,negated_conjecture,
    ( ~ mother(X)
    | female(sex_of2(X)) ) ).

cnf(mother4,negated_conjecture,
    ( ~ parent(X)
    | ~ sex(X,Y)
    | ~ female(Y)
    | mother(X) ) ).

cnf(father1,negated_conjecture,
    ( ~ father(X)
    | parent(X) ) ).

cnf(father2,negated_conjecture,
    ( ~ father(X)
    | ~ mother(X) ) ).

cnf(father3,negated_conjecture,
    ( ~ parent(X)
    | mother(X)
    | father(X) ) ).

cnf(grandparent1,negated_conjecture,
    ( ~ grandparent(X)
    | parent(X) ) ).

cnf(grandparent2,negated_conjecture,
    ( ~ grandparent(X)
    | child(X,child_of2(X)) ) ).

cnf(grandparent3,negated_conjecture,
    ( ~ grandparent(X)
    | parent(child_of2(X)) ) ).

cnf(grandparent4,negated_conjecture,
    ( ~ parent(X)
    | ~ child(X,Y)
    | ~ parent(Y)
    | grandparent(X) ) ).

cnf(parent_with_sons_only1,negated_conjecture,
    ( ~ parent_with_sons_only(X)
    | parent(X) ) ).

cnf(parent_with_sons_only2,negated_conjecture,
    ( ~ parent_with_sons_only(X)
    | ~ child(X,Y)
    | child_with_parent(Y) ) ).

cnf(parent_with_sons_only3,negated_conjecture,
    ( ~ parent(X)
    | child(X,female_child_of(X))
    | parent_with_sons_only(X) ) ).

cnf(parent_with_sons_only4,negated_conjecture,
    ( ~ parent(X)
    | ~ child_with_parent(female_child_of(X))
    | parent_with_sons_only(X) ) ).

cnf(parent_with_sons_only5,negated_conjecture,
    ( ~ child_with_parent(Y)
    | sex(Y,sex_of3(Y)) ) ).

cnf(parent_with_sons_only6,negated_conjecture,
    ( ~ child_with_parent(Y)
    | male(sex_of3(Y)) ) ).

cnf(parent_with_sons_only7,negated_conjecture,
    ( ~ sex(Y,Z)
    | ~ male(Z)
    | child_with_parent(Y) ) ).

%--------------------------------------------------------------------------
