%--------------------------------------------------------------------------
% File     : NLP134-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : An old dirty white Chevy, problem 21
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
% Syntax   : Number of clauses     :   54 (   2 unt;  23 nHn;  49 RR)
%            Number of literals    :  199 (   0 equ; 123 neg)
%            Maximal clause size   :   23 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   27 (  27 usr;   1 prp; 0-4 aty)
%            Number of functors    :   17 (  17 usr;  12 con; 0-2 aty)
%            Number of variables   :   52 (   7 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP134+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc31) ).

cnf(clause2,negated_conjecture,
    actual_world(skc12) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | city(skc31,skc35) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | chevy(skc31,skc35) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | white(skc31,skc35) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | dirty(skc31,skc35) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | old(skc31,skc35) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | placename(skc31,skc36) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | hollywood_placename(skc31,skc36) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | event(skc31,skc33) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | present(skc31,skc33) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | barrel(skc31,skc33) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | lonely(skc31,skc34) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | street(skc31,skc34) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkC0
    | group(skc31,skc32) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkC0
    | two(skc31,skc32) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkC0
    | ssSkP0(skc32,skc31) ) ).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | event(skc12,skc14) ) ).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | present(skc12,skc14) ) ).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | barrel(skc12,skc14) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | old(skc12,skc17) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | dirty(skc12,skc17) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | white(skc12,skc17) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | chevy(skc12,skc17) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | lonely(skc12,skc15) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | street(skc12,skc15) ) ).

cnf(clause27,negated_conjecture,
    ( ~ ssSkC0
    | city(skc12,skc15) ) ).

cnf(clause28,negated_conjecture,
    ( ~ ssSkC0
    | hollywood_placename(skc12,skc16) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | placename(skc12,skc16) ) ).

cnf(clause30,negated_conjecture,
    ( ~ ssSkC0
    | group(skc12,skc13) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | two(skc12,skc13) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc13,skc12) ) ).

cnf(clause33,negated_conjecture,
    ( ssSkC0
    | agent(skc31,skc33,skc35) ) ).

cnf(clause34,negated_conjecture,
    ( ssSkC0
    | in(skc31,skc33,skc35) ) ).

cnf(clause35,negated_conjecture,
    ( ssSkC0
    | of(skc31,skc36,skc35) ) ).

cnf(clause36,negated_conjecture,
    ( ssSkC0
    | down(skc31,skc33,skc34) ) ).

cnf(clause37,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc12,skc14,skc17) ) ).

cnf(clause38,negated_conjecture,
    ( ~ ssSkC0
    | in(skc12,skc14,skc15) ) ).

cnf(clause39,negated_conjecture,
    ( ~ ssSkC0
    | down(skc12,skc14,skc15) ) ).

cnf(clause40,negated_conjecture,
    ( ~ ssSkC0
    | of(skc12,skc16,skc15) ) ).

cnf(clause41,negated_conjecture,
    ( ssSkP0(U,V)
    | member(V,skf11(V,U),U) ) ).

cnf(clause42,negated_conjecture,
    ( ~ member(skc31,U,skc32)
    | ssSkC0
    | fellow(skc31,U) ) ).

cnf(clause43,negated_conjecture,
    ( ~ member(skc31,U,skc32)
    | ssSkC0
    | young(skc31,U) ) ).

cnf(clause44,negated_conjecture,
    ( ~ member(skc12,U,skc13)
    | ~ ssSkC0
    | fellow(skc12,U) ) ).

cnf(clause45,negated_conjecture,
    ( ~ member(skc12,U,skc13)
    | ~ ssSkC0
    | young(skc12,U) ) ).

cnf(clause46,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | state(U,skf8(U,X)) ) ).

cnf(clause47,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | frontseat(U,skf7(U,X)) ) ).

cnf(clause48,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | in(U,skf7(U,X),skf7(U,X)) ) ).

cnf(clause49,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | be(U,skf8(U,V),V,skf7(U,V)) ) ).

cnf(clause50,negated_conjecture,
    ( ~ frontseat(U,V)
    | ~ in(U,V,V)
    | ~ be(U,W,skf11(U,X),V)
    | ~ state(U,W)
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
    ( ~ city(U,V)
    | ~ chevy(U,V)
    | ~ white(U,V)
    | ~ dirty(U,V)
    | ~ old(U,V)
    | ~ agent(U,W,V)
    | ~ in(U,W,V)
    | ~ placename(U,X)
    | ~ hollywood_placename(U,X)
    | ~ of(U,X,V)
    | ~ event(U,W)
    | ~ present(U,W)
    | ~ barrel(U,W)
    | ~ down(U,W,Y)
    | ~ lonely(U,Y)
    | ~ street(U,Y)
    | ~ group(U,Z)
    | ~ two(U,Z)
    | ~ ssSkP0(Z,U)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf6(U,Z),Z) ) ).

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
    ( ~ city(U,V)
    | ~ chevy(U,V)
    | ~ white(U,V)
    | ~ dirty(U,V)
    | ~ old(U,V)
    | ~ agent(U,W,V)
    | ~ in(U,W,V)
    | ~ placename(U,X)
    | ~ hollywood_placename(U,X)
    | ~ of(U,X,V)
    | ~ event(U,W)
    | ~ present(U,W)
    | ~ barrel(U,W)
    | ~ down(U,W,Y)
    | ~ lonely(U,Y)
    | ~ street(U,Y)
    | ~ young(U,skf6(U,Z))
    | ~ fellow(U,skf6(U,Z))
    | ~ group(U,X1)
    | ~ two(U,X1)
    | ~ ssSkP0(X1,U)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
