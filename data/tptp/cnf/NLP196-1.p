%--------------------------------------------------------------------------
% File     : NLP196-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : An old dirty white Chevy, problem 83
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "An old dirty white chevy barrels down a lonely street in
%            hollywood. Two young fellas are in the front seat. They are
%            wearing cheap black coats. Jules is behind the wheel."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v6.3.0, 0.33 v6.2.0, 0.20 v6.1.0, 0.00 v5.4.0, 0.22 v5.3.0, 0.29 v5.0.0, 0.38 v4.1.0, 0.29 v4.0.0, 0.38 v3.5.0, 0.29 v3.4.0, 0.33 v3.2.0, 0.60 v3.1.0, 0.57 v2.7.0, 0.60 v2.6.0, 0.50 v2.5.0, 0.67 v2.4.0
% Syntax   : Number of clauses     :   92 (   2 unt;  39 nHn;  78 RR)
%            Number of literals    :  345 (   0 equ; 215 neg)
%            Maximal clause size   :   36 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   40 (  40 usr;   1 prp; 0-4 aty)
%            Number of functors    :   34 (  34 usr;  25 con; 0-3 aty)
%            Number of variables   :  144 (  29 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP196+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc73) ).

cnf(clause2,negated_conjecture,
    actual_world(skc25) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | barrel(skc73,skc81) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | present(skc73,skc81) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | event(skc73,skc81) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | chevy(skc73,skc84) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | white(skc73,skc84) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | dirty(skc73,skc84) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | old(skc73,skc84) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | city(skc73,skc82) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | street(skc73,skc82) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | lonely(skc73,skc82) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | placename(skc73,skc83) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | hollywood_placename(skc73,skc83) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkC0
    | group(skc73,skc78) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkC0
    | two(skc73,skc79) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkC0
    | group(skc73,skc79) ) ).

cnf(clause18,negated_conjecture,
    ( ssSkC0
    | ssSkP0(skc79,skc73) ) ).

cnf(clause19,negated_conjecture,
    ( ssSkC0
    | frontseat(skc73,skc80) ) ).

cnf(clause20,negated_conjecture,
    ( ssSkC0
    | wheel(skc73,skc74) ) ).

cnf(clause21,negated_conjecture,
    ( ssSkC0
    | jules_forename(skc73,skc76) ) ).

cnf(clause22,negated_conjecture,
    ( ssSkC0
    | forename(skc73,skc76) ) ).

cnf(clause23,negated_conjecture,
    ( ssSkC0
    | man(skc73,skc77) ) ).

cnf(clause24,negated_conjecture,
    ( ssSkC0
    | state(skc73,skc75) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | event(skc25,skc34) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | present(skc25,skc34) ) ).

cnf(clause27,negated_conjecture,
    ( ~ ssSkC0
    | barrel(skc25,skc34) ) ).

cnf(clause28,negated_conjecture,
    ( ~ ssSkC0
    | old(skc25,skc37) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | dirty(skc25,skc37) ) ).

cnf(clause30,negated_conjecture,
    ( ~ ssSkC0
    | white(skc25,skc37) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | chevy(skc25,skc37) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | lonely(skc25,skc35) ) ).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | street(skc25,skc35) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | city(skc25,skc35) ) ).

cnf(clause35,negated_conjecture,
    ( ~ ssSkC0
    | hollywood_placename(skc25,skc36) ) ).

cnf(clause36,negated_conjecture,
    ( ~ ssSkC0
    | placename(skc25,skc36) ) ).

cnf(clause37,negated_conjecture,
    ( ~ ssSkC0
    | group(skc25,skc31) ) ).

cnf(clause38,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc32,skc25) ) ).

cnf(clause39,negated_conjecture,
    ( ~ ssSkC0
    | group(skc25,skc32) ) ).

cnf(clause40,negated_conjecture,
    ( ~ ssSkC0
    | two(skc25,skc32) ) ).

cnf(clause41,negated_conjecture,
    ( ~ ssSkC0
    | frontseat(skc25,skc33) ) ).

cnf(clause42,negated_conjecture,
    ( ~ ssSkC0
    | wheel(skc25,skc30) ) ).

cnf(clause43,negated_conjecture,
    ( ~ ssSkC0
    | state(skc25,skc27) ) ).

cnf(clause44,negated_conjecture,
    ( ~ ssSkC0
    | jules_forename(skc25,skc28) ) ).

cnf(clause45,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc25,skc28) ) ).

cnf(clause46,negated_conjecture,
    ( ~ ssSkC0
    | man(skc25,skc29) ) ).

cnf(clause47,negated_conjecture,
    ( ssSkC0
    | agent(skc73,skc81,skc84) ) ).

cnf(clause48,negated_conjecture,
    ( ssSkC0
    | down(skc73,skc81,skc82) ) ).

cnf(clause49,negated_conjecture,
    ( ssSkC0
    | in(skc73,skc81,skc82) ) ).

cnf(clause50,negated_conjecture,
    ( ssSkC0
    | of(skc73,skc83,skc82) ) ).

cnf(clause51,negated_conjecture,
    ( ssSkC0
    | ssSkP2(skc79,skc78,skc73) ) ).

cnf(clause52,negated_conjecture,
    ( ssSkC0
    | ssSkP1(skc80,skc79,skc73) ) ).

cnf(clause53,negated_conjecture,
    ( ssSkC0
    | behind(skc73,skc74,skc74) ) ).

cnf(clause54,negated_conjecture,
    ( ssSkC0
    | of(skc73,skc76,skc77) ) ).

cnf(clause55,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc25,skc34,skc37) ) ).

cnf(clause56,negated_conjecture,
    ( ~ ssSkC0
    | in(skc25,skc34,skc35) ) ).

cnf(clause57,negated_conjecture,
    ( ~ ssSkC0
    | down(skc25,skc34,skc35) ) ).

cnf(clause58,negated_conjecture,
    ( ~ ssSkC0
    | of(skc25,skc36,skc35) ) ).

cnf(clause59,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP2(skc32,skc31,skc25) ) ).

cnf(clause60,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP1(skc33,skc32,skc25) ) ).

cnf(clause61,negated_conjecture,
    ( ~ ssSkC0
    | behind(skc25,skc26,skc30) ) ).

cnf(clause62,negated_conjecture,
    ( ~ ssSkC0
    | of(skc25,skc28,skc29) ) ).

cnf(clause63,negated_conjecture,
    ( ssSkC0
    | be(skc73,skc75,skc77,skc74) ) ).

cnf(clause64,negated_conjecture,
    ( ~ ssSkC0
    | be(skc25,skc27,skc29,skc26) ) ).

cnf(clause65,negated_conjecture,
    ( ssSkP0(U,V)
    | member(V,skf11(V,U),U) ) ).

cnf(clause66,negated_conjecture,
    ( ~ member(skc73,U,skc78)
    | ssSkC0
    | coat(skc73,U) ) ).

cnf(clause67,negated_conjecture,
    ( ~ member(skc73,U,skc78)
    | ssSkC0
    | black(skc73,U) ) ).

cnf(clause68,negated_conjecture,
    ( ~ member(skc73,U,skc78)
    | ssSkC0
    | cheap(skc73,U) ) ).

cnf(clause69,negated_conjecture,
    ( ~ member(skc25,U,skc31)
    | ~ ssSkC0
    | coat(skc25,U) ) ).

cnf(clause70,negated_conjecture,
    ( ~ member(skc25,U,skc31)
    | ~ ssSkC0
    | black(skc25,U) ) ).

cnf(clause71,negated_conjecture,
    ( ~ member(skc25,U,skc31)
    | ~ ssSkC0
    | cheap(skc25,U) ) ).

cnf(clause72,negated_conjecture,
    ( ssSkP1(U,V,W)
    | member(W,skf16(U,W,V),V) ) ).

cnf(clause73,negated_conjecture,
    ( ssSkP2(U,V,W)
    | member(W,skf21(U,W,X),U) ) ).

cnf(clause74,negated_conjecture,
    ( ssSkP2(U,V,W)
    | member(W,skf19(U,W,V),V) ) ).

cnf(clause75,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | fellow(U,V) ) ).

cnf(clause76,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | young(U,V) ) ).

cnf(clause77,negated_conjecture,
    ( ~ young(U,skf11(U,V))
    | ~ fellow(U,skf11(U,V))
    | ssSkP0(W,U) ) ).

cnf(clause78,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | state(U,skf13(U,Y,Z)) ) ).

cnf(clause79,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | in(U,skf12(V,U,X),X) ) ).

cnf(clause80,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | be(U,skf13(U,Y,V),V,skf12(V,U,Y)) ) ).

cnf(clause81,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | wear(U,skf17(U,Z,X1)) ) ).

cnf(clause82,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | nonreflexive(U,skf17(U,Z,X1)) ) ).

cnf(clause83,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | present(U,skf17(U,Z,X1)) ) ).

cnf(clause84,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | event(U,skf17(U,Z,X1)) ) ).

cnf(clause85,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | agent(U,skf17(U,V,Z),V) ) ).

cnf(clause86,negated_conjecture,
    ( ~ in(U,V,W)
    | ~ be(U,X,skf16(W,U,Y),V)
    | ~ state(U,X)
    | ssSkP1(W,Z,U) ) ).

cnf(clause87,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | patient(U,skf17(U,V,X),X) ) ).

cnf(clause88,negated_conjecture,
    ( ~ wear(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf19(W,U,X))
    | ~ agent(U,V,skf21(W,U,X))
    | ~ event(U,V)
    | ssSkP2(W,Y,U) ) ).

cnf(clause89,negated_conjecture,
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
    | ~ ssSkP2(X1,Z,U)
    | ~ ssSkP0(X1,U)
    | ~ group(U,X1)
    | ~ two(U,X1)
    | ~ frontseat(U,X2)
    | ~ ssSkP1(X2,X1,U)
    | ~ behind(U,X3,X4)
    | ~ wheel(U,X4)
    | ~ state(U,X5)
    | ~ jules_forename(U,X6)
    | ~ forename(U,X6)
    | ~ be(U,X5,X7,X3)
    | ~ man(U,X7)
    | ~ of(U,X6,X7)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf23(U,Z),Z) ) ).

cnf(clause90,negated_conjecture,
    ( ~ barrel(U,V)
    | ~ present(U,V)
    | ~ event(U,V)
    | ~ chevy(U,W)
    | ~ white(U,W)
    | ~ dirty(U,W)
    | ~ old(U,W)
    | ~ agent(U,V,W)
    | ~ city(U,X)
    | ~ street(U,X)
    | ~ lonely(U,X)
    | ~ down(U,V,X)
    | ~ in(U,V,X)
    | ~ placename(U,Y)
    | ~ hollywood_placename(U,Y)
    | ~ of(U,Y,X)
    | ~ group(U,Z)
    | ~ two(U,X1)
    | ~ group(U,X1)
    | ~ ssSkP0(X1,U)
    | ~ ssSkP2(X1,Z,U)
    | ~ ssSkP1(X2,X1,U)
    | ~ frontseat(U,X2)
    | ~ behind(U,X3,X3)
    | ~ wheel(U,X3)
    | ~ jules_forename(U,X4)
    | ~ forename(U,X4)
    | ~ be(U,X5,X6,X3)
    | ~ man(U,X6)
    | ~ of(U,X4,X6)
    | ~ state(U,X5)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf10(U,Z),Z) ) ).

cnf(clause91,negated_conjecture,
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
    | ~ cheap(U,skf23(U,X1))
    | ~ black(U,skf23(U,X1))
    | ~ coat(U,skf23(U,X1))
    | ~ ssSkP2(X2,Z,U)
    | ~ ssSkP0(X2,U)
    | ~ group(U,X2)
    | ~ two(U,X2)
    | ~ frontseat(U,X3)
    | ~ ssSkP1(X3,X2,U)
    | ~ behind(U,X4,X5)
    | ~ wheel(U,X5)
    | ~ state(U,X6)
    | ~ jules_forename(U,X7)
    | ~ forename(U,X7)
    | ~ be(U,X6,X8,X4)
    | ~ man(U,X8)
    | ~ of(U,X7,X8)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause92,negated_conjecture,
    ( ~ barrel(U,V)
    | ~ present(U,V)
    | ~ event(U,V)
    | ~ chevy(U,W)
    | ~ white(U,W)
    | ~ dirty(U,W)
    | ~ old(U,W)
    | ~ agent(U,V,W)
    | ~ city(U,X)
    | ~ street(U,X)
    | ~ lonely(U,X)
    | ~ down(U,V,X)
    | ~ in(U,V,X)
    | ~ placename(U,Y)
    | ~ hollywood_placename(U,Y)
    | ~ of(U,Y,X)
    | ~ cheap(U,skf10(U,Z))
    | ~ black(U,skf10(U,Z))
    | ~ coat(U,skf10(U,Z))
    | ~ group(U,X1)
    | ~ two(U,X2)
    | ~ group(U,X2)
    | ~ ssSkP0(X2,U)
    | ~ ssSkP2(X2,X1,U)
    | ~ ssSkP1(X3,X2,U)
    | ~ frontseat(U,X3)
    | ~ behind(U,X4,X4)
    | ~ wheel(U,X4)
    | ~ jules_forename(U,X5)
    | ~ forename(U,X5)
    | ~ be(U,X6,X7,X4)
    | ~ man(U,X7)
    | ~ of(U,X5,X7)
    | ~ state(U,X6)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
