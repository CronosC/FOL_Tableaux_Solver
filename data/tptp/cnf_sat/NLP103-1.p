%--------------------------------------------------------------------------
% File     : NLP103-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Every customer in a restaurant, problem 10
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
% Syntax   : Number of clauses     :   38 (   2 unt;  17 nHn;  17 RR)
%            Number of literals    :  168 (   0 equ; 114 neg)
%            Maximal clause size   :   17 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   14 (  14 usr;   1 prp; 0-3 aty)
%            Number of functors    :   14 (  14 usr;   8 con; 0-3 aty)
%            Number of variables   :   70 (  25 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP103+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc20) ).

cnf(clause2,negated_conjecture,
    actual_world(skc8) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | event(skc20,skc21) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | past(skc20,skc21) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | nonreflexive(skc20,skc21) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | drink(skc20,skc21) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | coffee(skc20,skc25) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | human_person(skc20,skc22) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | restaurant(skc20,skc23) ) ).

cnf(clause10,negated_conjecture,
    ( ~ ssSkC0
    | coffee(skc8,skc9) ) ).

cnf(clause11,negated_conjecture,
    ( ~ ssSkC0
    | restaurant(skc8,skc10) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | patient(skc20,skc21,skc25) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | agent(skc20,skc21,skc22) ) ).

cnf(clause14,negated_conjecture,
    ( ~ in(skc20,U,skc23)
    | ~ customer(skc20,U)
    | ssSkC0
    | event(skc20,skf16(V)) ) ).

cnf(clause15,negated_conjecture,
    ( ~ in(skc20,U,skc23)
    | ~ customer(skc20,U)
    | ssSkC0
    | past(skc20,skf16(V)) ) ).

cnf(clause16,negated_conjecture,
    ( ~ in(skc20,U,skc23)
    | ~ customer(skc20,U)
    | ssSkC0
    | nonreflexive(skc20,skf16(V)) ) ).

cnf(clause17,negated_conjecture,
    ( ~ in(skc20,U,skc23)
    | ~ customer(skc20,U)
    | ssSkC0
    | see(skc20,skf16(V)) ) ).

cnf(clause18,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | human_person(skc8,skf10(V)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | drink(skc8,skf9(V)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | nonreflexive(skc8,skf9(V)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | past(skc8,skf9(V)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | event(skc8,skf9(V)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | event(skc8,skf8(V)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | past(skc8,skf8(V)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | nonreflexive(skc8,skf8(V)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | see(skc8,skf8(V)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ in(skc20,U,skc23)
    | ~ customer(skc20,U)
    | ssSkC0
    | agent(skc20,skf16(U),U) ) ).

cnf(clause28,negated_conjecture,
    ( ~ in(skc20,U,skc23)
    | ~ customer(skc20,U)
    | ssSkC0
    | patient(skc20,skf16(V),skc22) ) ).

cnf(clause29,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | patient(skc8,skf9(V),skc9) ) ).

cnf(clause30,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | agent(skc8,skf8(U),U) ) ).

cnf(clause31,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | agent(skc8,skf9(V),skf10(V)) ) ).

cnf(clause32,negated_conjecture,
    ( ~ in(skc8,U,skc10)
    | ~ customer(skc8,U)
    | ~ ssSkC0
    | patient(skc8,skf8(V),skf10(V)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ restaurant(U,W)
    | ~ actual_world(U)
    | ssSkC0
    | customer(U,skf20(U,X,Y)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ restaurant(U,W)
    | ~ actual_world(U)
    | ssSkC0
    | in(U,skf20(U,W,X),W) ) ).

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
    | customer(U,skf12(U,Z,X1)) ) ).

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
    | in(U,skf12(U,Y,Z),Y) ) ).

cnf(clause37,negated_conjecture,
    ( ~ coffee(U,V)
    | ~ see(U,W)
    | ~ nonreflexive(U,W)
    | ~ past(U,W)
    | ~ agent(U,W,skf20(U,X,V))
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
    | ~ agent(U,Z,skf12(U,Y,X))
    | ~ event(U,Z)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
