%--------------------------------------------------------------------------
% File     : NLP136-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : An old dirty white Chevy, problem 23
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "An old dirty white chevy barrels down a lonely street in
%            hollywood. Two young fellas are in the front seat."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0, 0.33 v2.4.0
% Syntax   : Number of clauses     :   54 (   2 unt;  24 nHn;  50 RR)
%            Number of literals    :  200 (   0 equ; 123 neg)
%            Maximal clause size   :   23 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   27 (  27 usr;   1 prp; 0-4 aty)
%            Number of functors    :   18 (  18 usr;  13 con; 0-2 aty)
%            Number of variables   :   52 (   4 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP136+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc33) ).

cnf(clause2,negated_conjecture,
    actual_world(skc13) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | old(skc33,skc39) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | dirty(skc33,skc39) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | white(skc33,skc39) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | chevy(skc33,skc39) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | barrel(skc33,skc35) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | present(skc33,skc35) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | event(skc33,skc35) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | hollywood_placename(skc33,skc37) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | placename(skc33,skc37) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | city(skc33,skc38) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | street(skc33,skc36) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | lonely(skc33,skc36) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkC0
    | ssSkP0(skc34,skc33) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkC0
    | two(skc33,skc34) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkC0
    | group(skc33,skc34) ) ).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | event(skc13,skc15) ) ).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | present(skc13,skc15) ) ).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | barrel(skc13,skc15) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | old(skc13,skc18) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | dirty(skc13,skc18) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | white(skc13,skc18) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | chevy(skc13,skc18) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | lonely(skc13,skc16) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | street(skc13,skc16) ) ).

cnf(clause27,negated_conjecture,
    ( ~ ssSkC0
    | city(skc13,skc16) ) ).

cnf(clause28,negated_conjecture,
    ( ~ ssSkC0
    | hollywood_placename(skc13,skc17) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | placename(skc13,skc17) ) ).

cnf(clause30,negated_conjecture,
    ( ~ ssSkC0
    | group(skc13,skc14) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | two(skc13,skc14) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc14,skc13) ) ).

cnf(clause33,negated_conjecture,
    ( ssSkC0
    | agent(skc33,skc35,skc39) ) ).

cnf(clause34,negated_conjecture,
    ( ssSkC0
    | in(skc33,skc35,skc38) ) ).

cnf(clause35,negated_conjecture,
    ( ssSkC0
    | of(skc33,skc37,skc38) ) ).

cnf(clause36,negated_conjecture,
    ( ssSkC0
    | down(skc33,skc35,skc36) ) ).

cnf(clause37,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc13,skc15,skc18) ) ).

cnf(clause38,negated_conjecture,
    ( ~ ssSkC0
    | in(skc13,skc15,skc16) ) ).

cnf(clause39,negated_conjecture,
    ( ~ ssSkC0
    | down(skc13,skc15,skc16) ) ).

cnf(clause40,negated_conjecture,
    ( ~ ssSkC0
    | of(skc13,skc17,skc16) ) ).

cnf(clause41,negated_conjecture,
    ( ssSkP0(U,V)
    | frontseat(V,skf11(V,W)) ) ).

cnf(clause42,negated_conjecture,
    ( ssSkP0(U,V)
    | member(V,skf11(V,U),U) ) ).

cnf(clause43,negated_conjecture,
    ( ~ member(skc33,U,skc34)
    | ssSkC0
    | fellow(skc33,U) ) ).

cnf(clause44,negated_conjecture,
    ( ~ member(skc33,U,skc34)
    | ssSkC0
    | young(skc33,U) ) ).

cnf(clause45,negated_conjecture,
    ( ~ member(skc13,U,skc14)
    | ~ ssSkC0
    | fellow(skc13,U) ) ).

cnf(clause46,negated_conjecture,
    ( ~ member(skc13,U,skc14)
    | ~ ssSkC0
    | young(skc13,U) ) ).

cnf(clause47,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ frontseat(U,V)
    | ~ ssSkP0(W,U)
    | state(U,skf8(U,X)) ) ).

cnf(clause48,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ frontseat(U,V)
    | ~ ssSkP0(W,U)
    | in(U,skf7(V,U),V) ) ).

cnf(clause49,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ frontseat(U,V)
    | ~ ssSkP0(W,U)
    | be(U,skf8(U,V),V,skf7(V,U)) ) ).

cnf(clause50,negated_conjecture,
    ( ~ in(U,V,skf11(U,W))
    | ~ be(U,X,skf11(U,W),V)
    | ~ state(U,X)
    | ssSkP0(Y,U) ) ).

cnf(clause51,negated_conjecture,
    ( ~ event(U,V)
    | ~ present(U,V)
    | ~ barrel(U,V)
    | ~ agent(U,V,W)
    | ~ old(U,W)
    | ~ dirty(U,W)
    | ~ white(U,W)
    | ~ chevy(U,W)
    | ~ in(U,V,X)
    | ~ down(U,V,X)
    | ~ lonely(U,X)
    | ~ street(U,X)
    | ~ city(U,X)
    | ~ of(U,Y,X)
    | ~ hollywood_placename(U,Y)
    | ~ placename(U,Y)
    | ~ group(U,Z)
    | ~ two(U,Z)
    | ~ ssSkP0(Z,U)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf13(U,Z),Z) ) ).

cnf(clause52,negated_conjecture,
    ( ~ agent(U,V,W)
    | ~ old(U,W)
    | ~ dirty(U,W)
    | ~ white(U,W)
    | ~ chevy(U,W)
    | ~ barrel(U,V)
    | ~ present(U,V)
    | ~ event(U,V)
    | ~ hollywood_placename(U,X)
    | ~ placename(U,X)
    | ~ in(U,V,Y)
    | ~ city(U,Y)
    | ~ of(U,X,Y)
    | ~ street(U,Z)
    | ~ lonely(U,Z)
    | ~ down(U,V,Z)
    | ~ ssSkP0(X1,U)
    | ~ two(U,X1)
    | ~ group(U,X1)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf6(U,X1),X1) ) ).

cnf(clause53,negated_conjecture,
    ( ~ event(U,V)
    | ~ present(U,V)
    | ~ barrel(U,V)
    | ~ agent(U,V,W)
    | ~ old(U,W)
    | ~ dirty(U,W)
    | ~ white(U,W)
    | ~ chevy(U,W)
    | ~ in(U,V,X)
    | ~ down(U,V,X)
    | ~ lonely(U,X)
    | ~ street(U,X)
    | ~ city(U,X)
    | ~ of(U,Y,X)
    | ~ hollywood_placename(U,Y)
    | ~ placename(U,Y)
    | ~ young(U,skf13(U,Z))
    | ~ fellow(U,skf13(U,Z))
    | ~ group(U,X1)
    | ~ two(U,X1)
    | ~ ssSkP0(X1,U)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause54,negated_conjecture,
    ( ~ agent(U,V,W)
    | ~ old(U,W)
    | ~ dirty(U,W)
    | ~ white(U,W)
    | ~ chevy(U,W)
    | ~ barrel(U,V)
    | ~ present(U,V)
    | ~ event(U,V)
    | ~ hollywood_placename(U,X)
    | ~ placename(U,X)
    | ~ in(U,V,Y)
    | ~ city(U,Y)
    | ~ of(U,X,Y)
    | ~ street(U,Z)
    | ~ lonely(U,Z)
    | ~ down(U,V,Z)
    | ~ ssSkP0(X1,U)
    | ~ two(U,X1)
    | ~ group(U,X1)
    | ~ young(U,skf6(U,X2))
    | ~ fellow(U,skf6(U,X2))
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
