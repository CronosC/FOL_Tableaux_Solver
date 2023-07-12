%--------------------------------------------------------------------------
% File     : NLP094-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Every customer in a restaurant, problem 1
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Every customer in a restaurant saw a person who drank a
%            coffee."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v4.0.0, 0.14 v3.4.0, 0.25 v3.3.0, 0.33 v3.2.0, 0.00 v3.1.0, 0.17 v2.7.0, 0.12 v2.6.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   38 (   2 unt;  17 nHn;  12 RR)
%            Number of literals    :  192 (   0 equ; 138 neg)
%            Maximal clause size   :   16 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   14 (  14 usr;   1 prp; 0-3 aty)
%            Number of functors    :   14 (  14 usr;   2 con; 0-1 aty)
%            Number of variables   :   98 (  20 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created from NLP094+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc13) ).

cnf(clause2,negated_conjecture,
    actual_world(skc2) ).

cnf(clause3,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | customer(U,skf39(U)) ) ).

cnf(clause4,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | restaurant(U,skf34(U)) ) ).

cnf(clause5,negated_conjecture,
    ( ~ actual_world(U)
    | ~ ssSkC0
    | customer(U,skf25(U)) ) ).

cnf(clause6,negated_conjecture,
    ( ~ actual_world(U)
    | ~ ssSkC0
    | restaurant(U,skf20(U)) ) ).

cnf(clause7,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | in(U,skf39(U),skf34(U)) ) ).

cnf(clause8,negated_conjecture,
    ( ~ actual_world(U)
    | ~ ssSkC0
    | in(U,skf25(U),skf20(U)) ) ).

cnf(clause9,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | event(skc13,skf26(W)) ) ).

cnf(clause10,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | past(skc13,skf26(W)) ) ).

cnf(clause11,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | nonreflexive(skc13,skf26(W)) ) ).

cnf(clause12,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | see(skc13,skf26(W)) ) ).

cnf(clause13,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | human_person(skc13,skf29(W)) ) ).

cnf(clause14,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | drink(skc13,skf27(W)) ) ).

cnf(clause15,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | nonreflexive(skc13,skf27(W)) ) ).

cnf(clause16,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | past(skc13,skf27(W)) ) ).

cnf(clause17,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | event(skc13,skf27(W)) ) ).

cnf(clause18,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | coffee(skc13,skf28(W)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | event(skc2,skf12(W)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | past(skc2,skf12(W)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | nonreflexive(skc2,skf12(W)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | see(skc2,skf12(W)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | coffee(skc2,skf14(W)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | drink(skc2,skf13(W)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | nonreflexive(skc2,skf13(W)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | past(skc2,skf13(W)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | event(skc2,skf13(W)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | human_person(skc2,skf15(W)) ) ).

cnf(clause29,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | agent(skc13,skf26(V),V) ) ).

cnf(clause30,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | agent(skc2,skf12(V),V) ) ).

cnf(clause31,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | patient(skc13,skf26(W),skf29(W)) ) ).

cnf(clause32,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | agent(skc13,skf27(W),skf29(W)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ restaurant(skc13,U)
    | ~ in(skc13,V,U)
    | ~ customer(skc13,V)
    | ssSkC0
    | patient(skc13,skf27(W),skf28(W)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | agent(skc2,skf13(W),skf15(W)) ) ).

cnf(clause35,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | patient(skc2,skf12(W),skf15(W)) ) ).

cnf(clause36,negated_conjecture,
    ( ~ restaurant(skc2,U)
    | ~ in(skc2,V,U)
    | ~ customer(skc2,V)
    | ~ ssSkC0
    | patient(skc2,skf13(W),skf14(W)) ) ).

cnf(clause37,negated_conjecture,
    ( ~ event(U,V)
    | ~ agent(U,V,skf39(U))
    | ~ past(U,V)
    | ~ nonreflexive(U,V)
    | ~ see(U,V)
    | ~ patient(U,W,X)
    | ~ coffee(U,X)
    | ~ drink(U,W)
    | ~ nonreflexive(U,W)
    | ~ past(U,W)
    | ~ event(U,W)
    | ~ human_person(U,Y)
    | ~ agent(U,W,Y)
    | ~ patient(U,V,Y)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause38,negated_conjecture,
    ( ~ event(U,V)
    | ~ agent(U,V,skf25(U))
    | ~ past(U,V)
    | ~ nonreflexive(U,V)
    | ~ see(U,V)
    | ~ patient(U,V,W)
    | ~ agent(U,X,W)
    | ~ human_person(U,W)
    | ~ drink(U,X)
    | ~ nonreflexive(U,X)
    | ~ past(U,X)
    | ~ event(U,X)
    | ~ coffee(U,Y)
    | ~ patient(U,X,Y)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
