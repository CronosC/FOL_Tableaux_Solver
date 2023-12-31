%--------------------------------------------------------------------------
% File     : NLP199-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : An old dirty white Chevy, problem 86
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
% Rating   : 0.00 v5.4.0, 0.22 v5.3.0, 0.29 v5.0.0, 0.25 v4.1.0, 0.14 v4.0.0, 0.25 v3.5.0, 0.29 v3.4.0, 0.33 v3.2.0, 0.60 v3.1.0, 0.57 v2.7.0, 0.60 v2.6.0, 0.50 v2.5.0, 0.67 v2.4.0
% Syntax   : Number of clauses     :   92 (   2 unt;  39 nHn;  78 RR)
%            Number of literals    :  345 (   0 equ; 215 neg)
%            Maximal clause size   :   36 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   40 (  40 usr;   1 prp; 0-4 aty)
%            Number of functors    :   33 (  33 usr;  24 con; 0-3 aty)
%            Number of variables   :  142 (  29 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP199+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc71) ).

cnf(clause2,negated_conjecture,
    actual_world(skc24) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | barrel(skc71,skc79) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | present(skc71,skc79) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | event(skc71,skc79) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | chevy(skc71,skc82) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | white(skc71,skc82) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | dirty(skc71,skc82) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | old(skc71,skc82) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | city(skc71,skc80) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | street(skc71,skc80) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | lonely(skc71,skc80) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | placename(skc71,skc81) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | hollywood_placename(skc71,skc81) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkC0
    | group(skc71,skc76) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkC0
    | two(skc71,skc77) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkC0
    | group(skc71,skc77) ) ).

cnf(clause18,negated_conjecture,
    ( ssSkC0
    | ssSkP0(skc77,skc71) ) ).

cnf(clause19,negated_conjecture,
    ( ssSkC0
    | frontseat(skc71,skc78) ) ).

cnf(clause20,negated_conjecture,
    ( ssSkC0
    | wheel(skc71,skc72) ) ).

cnf(clause21,negated_conjecture,
    ( ssSkC0
    | jules_forename(skc71,skc74) ) ).

cnf(clause22,negated_conjecture,
    ( ssSkC0
    | forename(skc71,skc74) ) ).

cnf(clause23,negated_conjecture,
    ( ssSkC0
    | man(skc71,skc75) ) ).

cnf(clause24,negated_conjecture,
    ( ssSkC0
    | state(skc71,skc73) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | barrel(skc24,skc32) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | present(skc24,skc32) ) ).

cnf(clause27,negated_conjecture,
    ( ~ ssSkC0
    | event(skc24,skc32) ) ).

cnf(clause28,negated_conjecture,
    ( ~ ssSkC0
    | chevy(skc24,skc35) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | white(skc24,skc35) ) ).

cnf(clause30,negated_conjecture,
    ( ~ ssSkC0
    | dirty(skc24,skc35) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | old(skc24,skc35) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | city(skc24,skc33) ) ).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | street(skc24,skc33) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | lonely(skc24,skc33) ) ).

cnf(clause35,negated_conjecture,
    ( ~ ssSkC0
    | placename(skc24,skc34) ) ).

cnf(clause36,negated_conjecture,
    ( ~ ssSkC0
    | hollywood_placename(skc24,skc34) ) ).

cnf(clause37,negated_conjecture,
    ( ~ ssSkC0
    | group(skc24,skc29) ) ).

cnf(clause38,negated_conjecture,
    ( ~ ssSkC0
    | two(skc24,skc30) ) ).

cnf(clause39,negated_conjecture,
    ( ~ ssSkC0
    | group(skc24,skc30) ) ).

cnf(clause40,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc30,skc24) ) ).

cnf(clause41,negated_conjecture,
    ( ~ ssSkC0
    | frontseat(skc24,skc31) ) ).

cnf(clause42,negated_conjecture,
    ( ~ ssSkC0
    | wheel(skc24,skc31) ) ).

cnf(clause43,negated_conjecture,
    ( ~ ssSkC0
    | jules_forename(skc24,skc27) ) ).

cnf(clause44,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc24,skc27) ) ).

cnf(clause45,negated_conjecture,
    ( ~ ssSkC0
    | man(skc24,skc28) ) ).

cnf(clause46,negated_conjecture,
    ( ~ ssSkC0
    | state(skc24,skc26) ) ).

cnf(clause47,negated_conjecture,
    ( ssSkC0
    | agent(skc71,skc79,skc82) ) ).

cnf(clause48,negated_conjecture,
    ( ssSkC0
    | down(skc71,skc79,skc80) ) ).

cnf(clause49,negated_conjecture,
    ( ssSkC0
    | in(skc71,skc79,skc80) ) ).

cnf(clause50,negated_conjecture,
    ( ssSkC0
    | of(skc71,skc81,skc80) ) ).

cnf(clause51,negated_conjecture,
    ( ssSkC0
    | ssSkP2(skc77,skc76,skc71) ) ).

cnf(clause52,negated_conjecture,
    ( ssSkC0
    | ssSkP1(skc78,skc77,skc71) ) ).

cnf(clause53,negated_conjecture,
    ( ssSkC0
    | behind(skc71,skc72,skc72) ) ).

cnf(clause54,negated_conjecture,
    ( ssSkC0
    | of(skc71,skc74,skc75) ) ).

cnf(clause55,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc24,skc32,skc35) ) ).

cnf(clause56,negated_conjecture,
    ( ~ ssSkC0
    | down(skc24,skc32,skc33) ) ).

cnf(clause57,negated_conjecture,
    ( ~ ssSkC0
    | in(skc24,skc32,skc33) ) ).

cnf(clause58,negated_conjecture,
    ( ~ ssSkC0
    | of(skc24,skc34,skc33) ) ).

cnf(clause59,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP2(skc30,skc29,skc24) ) ).

cnf(clause60,negated_conjecture,
    ( ~ ssSkC0
    | behind(skc24,skc25,skc31) ) ).

cnf(clause61,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP1(skc31,skc30,skc24) ) ).

cnf(clause62,negated_conjecture,
    ( ~ ssSkC0
    | of(skc24,skc27,skc28) ) ).

cnf(clause63,negated_conjecture,
    ( ssSkC0
    | be(skc71,skc73,skc75,skc72) ) ).

cnf(clause64,negated_conjecture,
    ( ~ ssSkC0
    | be(skc24,skc26,skc28,skc25) ) ).

cnf(clause65,negated_conjecture,
    ( ssSkP0(U,V)
    | member(V,skf12(V,U),U) ) ).

cnf(clause66,negated_conjecture,
    ( ~ member(skc71,U,skc76)
    | ssSkC0
    | coat(skc71,U) ) ).

cnf(clause67,negated_conjecture,
    ( ~ member(skc71,U,skc76)
    | ssSkC0
    | black(skc71,U) ) ).

cnf(clause68,negated_conjecture,
    ( ~ member(skc71,U,skc76)
    | ssSkC0
    | cheap(skc71,U) ) ).

cnf(clause69,negated_conjecture,
    ( ~ member(skc24,U,skc29)
    | ~ ssSkC0
    | coat(skc24,U) ) ).

cnf(clause70,negated_conjecture,
    ( ~ member(skc24,U,skc29)
    | ~ ssSkC0
    | black(skc24,U) ) ).

cnf(clause71,negated_conjecture,
    ( ~ member(skc24,U,skc29)
    | ~ ssSkC0
    | cheap(skc24,U) ) ).

cnf(clause72,negated_conjecture,
    ( ssSkP1(U,V,W)
    | member(W,skf17(U,W,V),V) ) ).

cnf(clause73,negated_conjecture,
    ( ssSkP2(U,V,W)
    | member(W,skf22(U,W,X),U) ) ).

cnf(clause74,negated_conjecture,
    ( ssSkP2(U,V,W)
    | member(W,skf20(U,W,V),V) ) ).

cnf(clause75,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | fellow(U,V) ) ).

cnf(clause76,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | young(U,V) ) ).

cnf(clause77,negated_conjecture,
    ( ~ young(U,skf12(U,V))
    | ~ fellow(U,skf12(U,V))
    | ssSkP0(W,U) ) ).

cnf(clause78,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | state(U,skf14(U,Y,Z)) ) ).

cnf(clause79,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | in(U,skf13(V,U,X),X) ) ).

cnf(clause80,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | be(U,skf14(U,Y,V),V,skf13(V,U,Y)) ) ).

cnf(clause81,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | wear(U,skf18(U,Z,X1)) ) ).

cnf(clause82,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | nonreflexive(U,skf18(U,Z,X1)) ) ).

cnf(clause83,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | present(U,skf18(U,Z,X1)) ) ).

cnf(clause84,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | event(U,skf18(U,Z,X1)) ) ).

cnf(clause85,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | agent(U,skf18(U,V,Z),V) ) ).

cnf(clause86,negated_conjecture,
    ( ~ in(U,V,W)
    | ~ be(U,X,skf17(W,U,Y),V)
    | ~ state(U,X)
    | ssSkP1(W,Z,U) ) ).

cnf(clause87,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | patient(U,skf18(U,V,X),X) ) ).

cnf(clause88,negated_conjecture,
    ( ~ wear(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf20(W,U,X))
    | ~ agent(U,V,skf22(W,U,X))
    | ~ event(U,V)
    | ssSkP2(W,Y,U) ) ).

cnf(clause89,negated_conjecture,
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
    | ~ behind(U,X2,X3)
    | ~ ssSkP1(X3,X1,U)
    | ~ frontseat(U,X3)
    | ~ wheel(U,X3)
    | ~ jules_forename(U,X4)
    | ~ forename(U,X4)
    | ~ be(U,X5,X6,X2)
    | ~ man(U,X6)
    | ~ of(U,X4,X6)
    | ~ state(U,X5)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf24(U,Z),Z) ) ).

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
    | member(U,skf11(U,Z),Z) ) ).

cnf(clause91,negated_conjecture,
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
    | ~ cheap(U,skf24(U,Z))
    | ~ black(U,skf24(U,Z))
    | ~ coat(U,skf24(U,Z))
    | ~ group(U,X1)
    | ~ two(U,X2)
    | ~ group(U,X2)
    | ~ ssSkP0(X2,U)
    | ~ ssSkP2(X2,X1,U)
    | ~ behind(U,X3,X4)
    | ~ ssSkP1(X4,X2,U)
    | ~ frontseat(U,X4)
    | ~ wheel(U,X4)
    | ~ jules_forename(U,X5)
    | ~ forename(U,X5)
    | ~ be(U,X6,X7,X3)
    | ~ man(U,X7)
    | ~ of(U,X5,X7)
    | ~ state(U,X6)
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
    | ~ cheap(U,skf11(U,Z))
    | ~ black(U,skf11(U,Z))
    | ~ coat(U,skf11(U,Z))
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
