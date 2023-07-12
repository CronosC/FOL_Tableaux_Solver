%--------------------------------------------------------------------------
% File     : NLP100-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Every customer in a restaurant, problem 7
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
% Syntax   : Number of clauses     :   38 (   2 unt;  18 nHn;  18 RR)
%            Number of literals    :  180 (   0 equ; 125 neg)
%            Maximal clause size   :   17 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   14 (  14 usr;   1 prp; 0-3 aty)
%            Number of functors    :   14 (  14 usr;   6 con; 0-3 aty)
%            Number of variables   :   79 (  19 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP100+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc17) ).

cnf(clause2,negated_conjecture,
    actual_world(skc6) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | event(skc17,skc18) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | past(skc17,skc18) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | nonreflexive(skc17,skc18) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | drink(skc17,skc18) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | coffee(skc17,skc22) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | human_person(skc17,skc19) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | restaurant(skc17,skc20) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | patient(skc17,skc18,skc22) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | agent(skc17,skc18,skc19) ) ).

cnf(clause12,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | customer(U,skf27(U)) ) ).

cnf(clause13,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | restaurant(U,skf22(U)) ) ).

cnf(clause14,negated_conjecture,
    ( ~ actual_world(U)
    | ssSkC0
    | in(U,skf27(U),skf22(U)) ) ).

cnf(clause15,negated_conjecture,
    ( ~ in(skc17,U,skc20)
    | ~ customer(skc17,U)
    | ssSkC0
    | event(skc17,skf17(V)) ) ).

cnf(clause16,negated_conjecture,
    ( ~ in(skc17,U,skc20)
    | ~ customer(skc17,U)
    | ssSkC0
    | past(skc17,skf17(V)) ) ).

cnf(clause17,negated_conjecture,
    ( ~ in(skc17,U,skc20)
    | ~ customer(skc17,U)
    | ssSkC0
    | nonreflexive(skc17,skf17(V)) ) ).

cnf(clause18,negated_conjecture,
    ( ~ in(skc17,U,skc20)
    | ~ customer(skc17,U)
    | ssSkC0
    | see(skc17,skf17(V)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ in(skc17,U,skc20)
    | ~ customer(skc17,U)
    | ssSkC0
    | agent(skc17,skf17(U),U) ) ).

cnf(clause20,negated_conjecture,
    ( ~ in(skc17,U,skc20)
    | ~ customer(skc17,U)
    | ssSkC0
    | patient(skc17,skf17(V),skc19) ) ).

cnf(clause21,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | event(skc6,skf8(W)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | past(skc6,skf8(W)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | nonreflexive(skc6,skf8(W)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | see(skc6,skf8(W)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | coffee(skc6,skf10(W)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | drink(skc6,skf9(W)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | nonreflexive(skc6,skf9(W)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | past(skc6,skf9(W)) ) ).

cnf(clause29,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | event(skc6,skf9(W)) ) ).

cnf(clause30,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | human_person(skc6,skf11(W)) ) ).

cnf(clause31,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | agent(skc6,skf8(V),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | agent(skc6,skf9(W),skf11(W)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | patient(skc6,skf8(W),skf11(W)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ restaurant(skc6,U)
    | ~ in(skc6,V,U)
    | ~ customer(skc6,V)
    | ~ ssSkC0
    | patient(skc6,skf9(W),skf10(W)) ) ).

cnf(clause35,negated_conjecture,
    ( ~ event(U,V)
    | ~ past(U,V)
    | ~ nonreflexive(U,V)
    | ~ drink(U,V)
    | ~ patient(U,V,W)
    | ~ coffee(U,W)
    | ~ agent(U,V,X)
    | ~ human_person(U,X)
    | ~ restaurant(U,Y)
    | ~ actual_world(U)
    | ~ ssSkC0
    | customer(U,skf13(U,Z,X1)) ) ).

cnf(clause36,negated_conjecture,
    ( ~ event(U,V)
    | ~ past(U,V)
    | ~ nonreflexive(U,V)
    | ~ drink(U,V)
    | ~ patient(U,V,W)
    | ~ coffee(U,W)
    | ~ agent(U,V,X)
    | ~ human_person(U,X)
    | ~ restaurant(U,Y)
    | ~ actual_world(U)
    | ~ ssSkC0
    | in(U,skf13(U,Y,Z),Y) ) ).

cnf(clause37,negated_conjecture,
    ( ~ event(U,V)
    | ~ agent(U,V,skf27(U))
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
    | ~ past(U,V)
    | ~ nonreflexive(U,V)
    | ~ drink(U,V)
    | ~ patient(U,V,W)
    | ~ coffee(U,W)
    | ~ agent(U,V,X)
    | ~ human_person(U,X)
    | ~ restaurant(U,Y)
    | ~ see(U,Z)
    | ~ nonreflexive(U,Z)
    | ~ past(U,Z)
    | ~ patient(U,Z,X)
    | ~ agent(U,Z,skf13(U,Y,X))
    | ~ event(U,Z)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
