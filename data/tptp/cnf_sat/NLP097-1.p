%--------------------------------------------------------------------------
% File     : NLP097-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Every customer in a restaurant, problem 4
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
% Syntax   : Number of clauses     :   38 (   2 unt;  18 nHn;  11 RR)
%            Number of literals    :  180 (   0 equ; 125 neg)
%            Maximal clause size   :   17 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   14 (  14 usr;   1 prp; 0-3 aty)
%            Number of functors    :   14 (  14 usr;   4 con; 0-3 aty)
%            Number of variables   :   89 (  26 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP097+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc15) ).

cnf(clause2,negated_conjecture,
    actual_world(skc4) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | coffee(skc15,skc16) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | restaurant(skc15,skc17) ) ).

cnf(clause5,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | customer(U,skf32(U)) ) ).

cnf(clause6,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | restaurant(U,skf27(U)) ) ).

cnf(clause7,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | in(U,skf32(U),skf27(U)) ) ).

cnf(clause8,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | human_person(skc15,skf22(V)) ) ).

cnf(clause9,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | drink(skc15,skf21(V)) ) ).

cnf(clause10,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | nonreflexive(skc15,skf21(V)) ) ).

cnf(clause11,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | past(skc15,skf21(V)) ) ).

cnf(clause12,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | event(skc15,skf21(V)) ) ).

cnf(clause13,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | event(skc15,skf20(V)) ) ).

cnf(clause14,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | past(skc15,skf20(V)) ) ).

cnf(clause15,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | nonreflexive(skc15,skf20(V)) ) ).

cnf(clause16,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | see(skc15,skf20(V)) ) ).

cnf(clause17,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | patient(skc15,skf21(V),skc16) ) ).

cnf(clause18,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | agent(skc15,skf20(U),U) ) ).

cnf(clause19,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | agent(skc15,skf21(V),skf22(V)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ in(skc15,U,skc17)
    | ~ customer(skc15,U)
    | ssSkC0
    | patient(skc15,skf20(V),skf22(V)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ restaurant(U,W)
    | ~ actual_world(U)
    | ~ ssSkC0
    | customer(U,skf17(U,X,Y)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | event(skc4,skf10(W)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | past(skc4,skf10(W)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | nonreflexive(skc4,skf10(W)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | see(skc4,skf10(W)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | coffee(skc4,skf12(W)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | drink(skc4,skf11(W)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | nonreflexive(skc4,skf11(W)) ) ).

cnf(clause29,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | past(skc4,skf11(W)) ) ).

cnf(clause30,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | event(skc4,skf11(W)) ) ).

cnf(clause31,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | human_person(skc4,skf13(W)) ) ).

cnf(clause32,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ restaurant(U,W)
    | ~ actual_world(U)
    | ~ ssSkC0
    | in(U,skf17(U,W,X),W) ) ).

cnf(clause33,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | agent(skc4,skf10(V),V) ) ).

cnf(clause34,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | patient(skc4,skf10(W),skf13(W)) ) ).

cnf(clause35,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | patient(skc4,skf11(W),skf12(W)) ) ).

cnf(clause36,negated_conjecture,
    ( ~ restaurant(skc4,U)
    | ~ in(skc4,V,U)
    | ~ customer(skc4,V)
    | ~ ssSkC0
    | agent(skc4,skf11(W),skf13(W)) ) ).

cnf(clause37,negated_conjecture,
    ( ~ event(U,V)
    | ~ agent(U,V,skf32(U))
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
    ( ~ coffee(U,V)
    | ~ see(U,W)
    | ~ nonreflexive(U,W)
    | ~ past(U,W)
    | ~ agent(U,W,skf17(U,X,V))
    | ~ event(U,W)
    | ~ event(U,Y)
    | ~ patient(U,Y,V)
    | ~ past(U,Y)
    | ~ nonreflexive(U,Y)
    | ~ drink(U,Y)
    | ~ patient(U,W,Z)
    | ~ agent(U,Y,Z)
    | ~ human_person(U,Z)
    | ~ restaurant(U,X)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
