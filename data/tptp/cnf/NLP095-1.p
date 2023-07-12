%--------------------------------------------------------------------------
% File     : NLP095-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Every customer in a restaurant, problem 2
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Every customer in a restaurant saw a person who drank a
%            coffee."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   38 (   2 unt;  17 nHn;  11 RR)
%            Number of literals    :  192 (   0 equ; 138 neg)
%            Maximal clause size   :   16 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   14 (  14 usr;   1 prp; 0-3 aty)
%            Number of functors    :   14 (  14 usr;   3 con; 0-2 aty)
%            Number of variables   :  100 (  24 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP095+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc17) ).

cnf(clause2,negated_conjecture,
    actual_world(skc3) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | coffee(skc17,skc18) ) ).

cnf(clause4,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | customer(U,skf37(U)) ) ).

cnf(clause5,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | restaurant(U,skf32(U)) ) ).

cnf(clause6,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | in(U,skf37(U),skf32(U)) ) ).

cnf(clause7,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ actual_world(U)
    | ~ ssSkC0
    | restaurant(U,skf18(U,W)) ) ).

cnf(clause8,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ actual_world(U)
    | ~ ssSkC0
    | customer(U,skf22(U,W)) ) ).

cnf(clause9,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ actual_world(U)
    | ~ ssSkC0
    | in(U,skf22(U,V),skf18(U,V)) ) ).

cnf(clause10,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | see(skc17,skf25(W)) ) ).

cnf(clause11,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | nonreflexive(skc17,skf25(W)) ) ).

cnf(clause12,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | past(skc17,skf25(W)) ) ).

cnf(clause13,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | event(skc17,skf25(W)) ) ).

cnf(clause14,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | event(skc17,skf26(W)) ) ).

cnf(clause15,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | past(skc17,skf26(W)) ) ).

cnf(clause16,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | nonreflexive(skc17,skf26(W)) ) ).

cnf(clause17,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | drink(skc17,skf26(W)) ) ).

cnf(clause18,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | human_person(skc17,skf27(W)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | event(skc3,skf11(W)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | past(skc3,skf11(W)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | nonreflexive(skc3,skf11(W)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | see(skc3,skf11(W)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | coffee(skc3,skf13(W)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | drink(skc3,skf12(W)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | nonreflexive(skc3,skf12(W)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | past(skc3,skf12(W)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | event(skc3,skf12(W)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | human_person(skc3,skf14(W)) ) ).

cnf(clause29,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | agent(skc17,skf25(V),V) ) ).

cnf(clause30,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | patient(skc17,skf26(W),skc18) ) ).

cnf(clause31,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | agent(skc3,skf11(V),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | patient(skc17,skf25(W),skf27(W)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ restaurant(skc17,U)
    | ~ in(skc17,V,U)
    | ~ customer(skc17,V)
    | ssSkC0
    | agent(skc17,skf26(W),skf27(W)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | patient(skc3,skf12(W),skf13(W)) ) ).

cnf(clause35,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | agent(skc3,skf12(W),skf14(W)) ) ).

cnf(clause36,negated_conjecture,
    ( ~ restaurant(skc3,U)
    | ~ in(skc3,V,U)
    | ~ customer(skc3,V)
    | ~ ssSkC0
    | patient(skc3,skf11(W),skf14(W)) ) ).

cnf(clause37,negated_conjecture,
    ( ~ event(U,V)
    | ~ agent(U,V,skf37(U))
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
    ( ~ see(U,V)
    | ~ nonreflexive(U,V)
    | ~ past(U,V)
    | ~ agent(U,V,skf22(U,W))
    | ~ event(U,V)
    | ~ event(U,X)
    | ~ patient(U,X,W)
    | ~ past(U,X)
    | ~ nonreflexive(U,X)
    | ~ drink(U,X)
    | ~ patient(U,V,Y)
    | ~ agent(U,X,Y)
    | ~ human_person(U,Y)
    | ~ coffee(U,W)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
