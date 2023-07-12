%--------------------------------------------------------------------------
% File     : NLP102-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Every customer in a restaurant, problem 9
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
% Syntax   : Number of clauses     :   38 (   2 unt;  18 nHn;  17 RR)
%            Number of literals    :  180 (   0 equ; 125 neg)
%            Maximal clause size   :   17 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   14 (  14 usr;   1 prp; 0-3 aty)
%            Number of functors    :   14 (  14 usr;   7 con; 0-3 aty)
%            Number of variables   :   81 (  23 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP102+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc18) ).

cnf(clause2,negated_conjecture,
    actual_world(skc7) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | event(skc18,skc19) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | past(skc18,skc19) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | nonreflexive(skc18,skc19) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | drink(skc18,skc19) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | coffee(skc18,skc23) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | human_person(skc18,skc20) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | restaurant(skc18,skc21) ) ).

cnf(clause10,negated_conjecture,
    ( ~ ssSkC0
    | coffee(skc7,skc8) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | patient(skc18,skc19,skc23) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | agent(skc18,skc19,skc20) ) ).

cnf(clause13,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ actual_world(U)
    | ssSkC0
    | restaurant(U,skf21(U,W)) ) ).

cnf(clause14,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ actual_world(U)
    | ssSkC0
    | customer(U,skf25(U,W)) ) ).

cnf(clause15,negated_conjecture,
    ( ~ in(skc18,U,skc21)
    | ~ customer(skc18,U)
    | ssSkC0
    | event(skc18,skf17(V)) ) ).

cnf(clause16,negated_conjecture,
    ( ~ in(skc18,U,skc21)
    | ~ customer(skc18,U)
    | ssSkC0
    | past(skc18,skf17(V)) ) ).

cnf(clause17,negated_conjecture,
    ( ~ in(skc18,U,skc21)
    | ~ customer(skc18,U)
    | ssSkC0
    | nonreflexive(skc18,skf17(V)) ) ).

cnf(clause18,negated_conjecture,
    ( ~ in(skc18,U,skc21)
    | ~ customer(skc18,U)
    | ssSkC0
    | see(skc18,skf17(V)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ in(skc18,U,skc21)
    | ~ customer(skc18,U)
    | ssSkC0
    | agent(skc18,skf17(U),U) ) ).

cnf(clause20,negated_conjecture,
    ( ~ in(skc18,U,skc21)
    | ~ customer(skc18,U)
    | ssSkC0
    | patient(skc18,skf17(V),skc20) ) ).

cnf(clause21,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ actual_world(U)
    | ssSkC0
    | in(U,skf25(U,V),skf21(U,V)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | see(skc7,skf9(W)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | nonreflexive(skc7,skf9(W)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | past(skc7,skf9(W)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | event(skc7,skf9(W)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | event(skc7,skf10(W)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | past(skc7,skf10(W)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | nonreflexive(skc7,skf10(W)) ) ).

cnf(clause29,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | drink(skc7,skf10(W)) ) ).

cnf(clause30,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | human_person(skc7,skf11(W)) ) ).

cnf(clause31,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | agent(skc7,skf9(V),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | patient(skc7,skf10(W),skc8) ) ).

cnf(clause33,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | patient(skc7,skf9(W),skf11(W)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ restaurant(skc7,U)
    | ~ in(skc7,V,U)
    | ~ customer(skc7,V)
    | ~ ssSkC0
    | agent(skc7,skf10(W),skf11(W)) ) ).

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
    ( ~ see(U,V)
    | ~ nonreflexive(U,V)
    | ~ past(U,V)
    | ~ agent(U,V,skf25(U,W))
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
