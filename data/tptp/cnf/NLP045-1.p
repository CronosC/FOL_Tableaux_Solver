%--------------------------------------------------------------------------
% File     : NLP045-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Mia ordered a shake, problem 4
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Mia ordered a shake. It cost five dollars."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0, 0.33 v2.4.0
% Syntax   : Number of clauses     :   46 (   2 unt;  18 nHn;  39 RR)
%            Number of literals    :  167 (   0 equ; 104 neg)
%            Maximal clause size   :   18 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   21 (  21 usr;   1 prp; 0-3 aty)
%            Number of functors    :   16 (  16 usr;  12 con; 0-3 aty)
%            Number of variables   :   69 (  22 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP045+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc33) ).

cnf(clause2,negated_conjecture,
    actual_world(skc12) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | group(skc33,skc34) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | five(skc33,skc34) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | nonhuman(skc33,skc37) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | mia_forename(skc33,skc37) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | forename(skc33,skc37) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | woman(skc33,skc38) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | event(skc33,skc35) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | past(skc33,skc35) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | nonreflexive(skc33,skc35) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | order(skc33,skc35) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | shake_beverage(skc33,skc36) ) ).

cnf(clause14,negated_conjecture,
    ( ~ ssSkC0
    | group(skc12,skc13) ) ).

cnf(clause15,negated_conjecture,
    ( ~ ssSkC0
    | five(skc12,skc13) ) ).

cnf(clause16,negated_conjecture,
    ( ~ ssSkC0
    | mia_forename(skc12,skc16) ) ).

cnf(clause17,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc12,skc16) ) ).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | woman(skc12,skc17) ) ).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | event(skc12,skc14) ) ).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | past(skc12,skc14) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | nonreflexive(skc12,skc14) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | order(skc12,skc14) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | shake_beverage(skc12,skc15) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | nonhuman(skc12,skc15) ) ).

cnf(clause25,negated_conjecture,
    ( ssSkC0
    | ssSkP0(skc37,skc34,skc33) ) ).

cnf(clause26,negated_conjecture,
    ( ssSkC0
    | agent(skc33,skc35,skc38) ) ).

cnf(clause27,negated_conjecture,
    ( ssSkC0
    | of(skc33,skc37,skc38) ) ).

cnf(clause28,negated_conjecture,
    ( ssSkC0
    | patient(skc33,skc35,skc36) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc12,skc14,skc17) ) ).

cnf(clause30,negated_conjecture,
    ( ~ ssSkC0
    | of(skc12,skc16,skc17) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc15,skc13,skc12) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | patient(skc12,skc14,skc15) ) ).

cnf(clause33,negated_conjecture,
    ( ~ member(skc33,U,skc34)
    | ssSkC0
    | dollar(skc33,U) ) ).

cnf(clause34,negated_conjecture,
    ( ~ member(skc12,U,skc13)
    | ~ ssSkC0
    | dollar(skc12,U) ) ).

cnf(clause35,negated_conjecture,
    ( ssSkP0(U,V,W)
    | member(W,skf8(U,W,V),V) ) ).

cnf(clause36,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,W,U)
    | event(U,skf6(U,Y,Z)) ) ).

cnf(clause37,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,W,U)
    | present(U,skf6(U,Y,Z)) ) ).

cnf(clause38,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,W,U)
    | nonreflexive(U,skf6(U,Y,Z)) ) ).

cnf(clause39,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,W,U)
    | cost(U,skf6(U,Y,Z)) ) ).

cnf(clause40,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,W,U)
    | agent(U,skf6(U,V,X),X) ) ).

cnf(clause41,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,W,U)
    | patient(U,skf6(U,V,Y),V) ) ).

cnf(clause42,negated_conjecture,
    ( ~ cost(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf8(W,U,X))
    | ~ agent(U,V,W)
    | ~ event(U,V)
    | ssSkP0(W,Y,U) ) ).

cnf(clause43,negated_conjecture,
    ( ~ group(U,V)
    | ~ five(U,V)
    | ~ mia_forename(U,W)
    | ~ forename(U,W)
    | ~ agent(U,X,Y)
    | ~ woman(U,Y)
    | ~ of(U,W,Y)
    | ~ event(U,X)
    | ~ past(U,X)
    | ~ nonreflexive(U,X)
    | ~ order(U,X)
    | ~ ssSkP0(Z,V,U)
    | ~ patient(U,X,Z)
    | ~ shake_beverage(U,Z)
    | ~ nonhuman(U,Z)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf10(U,V),V) ) ).

cnf(clause44,negated_conjecture,
    ( ~ dollar(U,skf10(U,V))
    | ~ group(U,W)
    | ~ five(U,W)
    | ~ mia_forename(U,X)
    | ~ forename(U,X)
    | ~ agent(U,Y,Z)
    | ~ woman(U,Z)
    | ~ of(U,X,Z)
    | ~ event(U,Y)
    | ~ past(U,Y)
    | ~ nonreflexive(U,Y)
    | ~ order(U,Y)
    | ~ ssSkP0(X1,W,U)
    | ~ patient(U,Y,X1)
    | ~ shake_beverage(U,X1)
    | ~ nonhuman(U,X1)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause45,negated_conjecture,
    ( ~ group(U,V)
    | ~ five(U,V)
    | ~ nonhuman(U,W)
    | ~ mia_forename(U,W)
    | ~ forename(U,W)
    | ~ ssSkP0(W,V,U)
    | ~ agent(U,X,Y)
    | ~ woman(U,Y)
    | ~ of(U,W,Y)
    | ~ event(U,X)
    | ~ past(U,X)
    | ~ nonreflexive(U,X)
    | ~ order(U,X)
    | ~ patient(U,X,Z)
    | ~ shake_beverage(U,Z)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf5(U,V),V) ) ).

cnf(clause46,negated_conjecture,
    ( ~ dollar(U,skf5(U,V))
    | ~ group(U,W)
    | ~ five(U,W)
    | ~ nonhuman(U,X)
    | ~ mia_forename(U,X)
    | ~ forename(U,X)
    | ~ ssSkP0(X,W,U)
    | ~ agent(U,Y,Z)
    | ~ woman(U,Z)
    | ~ of(U,X,Z)
    | ~ event(U,Y)
    | ~ past(U,Y)
    | ~ nonreflexive(U,Y)
    | ~ order(U,Y)
    | ~ patient(U,Y,X1)
    | ~ shake_beverage(U,X1)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
