%--------------------------------------------------------------------------
% File     : NLP108-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Every customer in a restaurant, problem 15
% Version  : [Bos00b] axioms.
% English  : Eliminating inconsistent interpretations in the statement
%            "Every customer in a restaurant saw a person who drank a
%            coffee."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v2.4.0
% Syntax   : Number of clauses     :   50 (  10 unt;   0 nHn;  45 RR)
%            Number of literals    :   99 (   0 equ;  53 neg)
%            Maximal clause size   :    4 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   33 (  33 usr;   0 prp; 1-3 aty)
%            Number of functors    :    6 (   6 usr;   5 con; 0-1 aty)
%            Number of variables   :   82 (   6 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP108+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,axiom,
    ( ~ see(U,V)
    | event(U,V) ) ).

cnf(clause2,axiom,
    ( ~ event(U,V)
    | eventuality(U,V) ) ).

cnf(clause3,axiom,
    ( ~ eventuality(U,V)
    | thing(U,V) ) ).

cnf(clause4,axiom,
    ( ~ thing(U,V)
    | singleton(U,V) ) ).

cnf(clause5,axiom,
    ( ~ eventuality(U,V)
    | specific(U,V) ) ).

cnf(clause6,axiom,
    ( ~ eventuality(U,V)
    | nonexistent(U,V) ) ).

cnf(clause7,axiom,
    ( ~ eventuality(U,V)
    | unisex(U,V) ) ).

cnf(clause8,axiom,
    ( ~ drink(U,V)
    | event(U,V) ) ).

cnf(clause9,axiom,
    ( ~ coffee(U,V)
    | beverage(U,V) ) ).

cnf(clause10,axiom,
    ( ~ beverage(U,V)
    | food(U,V) ) ).

cnf(clause11,axiom,
    ( ~ food(U,V)
    | substance_matter(U,V) ) ).

cnf(clause12,axiom,
    ( ~ substance_matter(U,V)
    | object(U,V) ) ).

cnf(clause13,axiom,
    ( ~ object(U,V)
    | entity(U,V) ) ).

cnf(clause14,axiom,
    ( ~ entity(U,V)
    | thing(U,V) ) ).

cnf(clause15,axiom,
    ( ~ entity(U,V)
    | specific(U,V) ) ).

cnf(clause16,axiom,
    ( ~ entity(U,V)
    | existent(U,V) ) ).

cnf(clause17,axiom,
    ( ~ object(U,V)
    | nonliving(U,V) ) ).

cnf(clause18,axiom,
    ( ~ object(U,V)
    | impartial(U,V) ) ).

cnf(clause19,axiom,
    ( ~ object(U,V)
    | unisex(U,V) ) ).

cnf(clause20,axiom,
    ( ~ human_person(U,V)
    | organism(U,V) ) ).

cnf(clause21,axiom,
    ( ~ organism(U,V)
    | entity(U,V) ) ).

cnf(clause22,axiom,
    ( ~ organism(U,V)
    | impartial(U,V) ) ).

cnf(clause23,axiom,
    ( ~ organism(U,V)
    | living(U,V) ) ).

cnf(clause24,axiom,
    ( ~ human_person(U,V)
    | human(U,V) ) ).

cnf(clause25,axiom,
    ( ~ human_person(U,V)
    | animate(U,V) ) ).

cnf(clause26,axiom,
    ( ~ customer(U,V)
    | human_person(U,V) ) ).

cnf(clause27,axiom,
    ( ~ restaurant(U,V)
    | building(U,V) ) ).

cnf(clause28,axiom,
    ( ~ building(U,V)
    | artifact(U,V) ) ).

cnf(clause29,axiom,
    ( ~ artifact(U,V)
    | object(U,V) ) ).

cnf(clause30,axiom,
    ( ~ living(U,V)
    | ~ nonliving(U,V) ) ).

cnf(clause31,axiom,
    ( ~ nonexistent(U,V)
    | ~ existent(U,V) ) ).

cnf(clause32,axiom,
    ( ~ nonliving(U,V)
    | ~ animate(U,V) ) ).

cnf(clause33,axiom,
    ( ~ nonreflexive(U,V)
    | ~ patient(U,V,W)
    | ~ agent(U,V,W) ) ).

cnf(clause34,axiom,
    ( ~ drink(U,V)
    | ~ patient(U,V,W)
    | ~ agent(U,V,X)
    | beverage(U,W) ) ).

cnf(clause35,negated_conjecture,
    actual_world(skc5) ).

cnf(clause36,negated_conjecture,
    coffee(skc5,skc10) ).

cnf(clause37,negated_conjecture,
    restaurant(skc5,skc8) ).

cnf(clause38,negated_conjecture,
    human_person(skc5,skc7) ).

cnf(clause39,negated_conjecture,
    drink(skc5,skc6) ).

cnf(clause40,negated_conjecture,
    nonreflexive(skc5,skc6) ).

cnf(clause41,negated_conjecture,
    past(skc5,skc6) ).

cnf(clause42,negated_conjecture,
    event(skc5,skc6) ).

cnf(clause43,negated_conjecture,
    agent(skc5,skc6,skc7) ).

cnf(clause44,negated_conjecture,
    patient(skc5,skc6,skc10) ).

cnf(clause45,negated_conjecture,
    ( ~ in(skc5,U,skc8)
    | ~ customer(skc5,U)
    | see(skc5,skf1(V)) ) ).

cnf(clause46,negated_conjecture,
    ( ~ in(skc5,U,skc8)
    | ~ customer(skc5,U)
    | nonreflexive(skc5,skf1(V)) ) ).

cnf(clause47,negated_conjecture,
    ( ~ in(skc5,U,skc8)
    | ~ customer(skc5,U)
    | past(skc5,skf1(V)) ) ).

cnf(clause48,negated_conjecture,
    ( ~ in(skc5,U,skc8)
    | ~ customer(skc5,U)
    | event(skc5,skf1(V)) ) ).

cnf(clause49,negated_conjecture,
    ( ~ in(skc5,U,skc8)
    | ~ customer(skc5,U)
    | patient(skc5,skf1(V),skc7) ) ).

cnf(clause50,negated_conjecture,
    ( ~ in(skc5,U,skc8)
    | ~ customer(skc5,U)
    | agent(skc5,skf1(U),U) ) ).

%--------------------------------------------------------------------------
