%--------------------------------------------------------------------------
% File     : NLP165-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : An old dirty white Chevy, problem 52
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "An old dirty white chevy barrels down a lonely street in
%            hollywood. Two young fellas are in the front seat. They are
%            wearing cheap black coats."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v5.4.0, 0.22 v5.3.0, 0.29 v5.0.0, 0.25 v4.1.0, 0.14 v4.0.0, 0.25 v3.5.0, 0.29 v3.4.0, 0.33 v3.2.0, 0.60 v3.1.0, 0.57 v2.7.0, 0.60 v2.6.0, 0.50 v2.5.0, 0.67 v2.4.0
% Syntax   : Number of clauses     :   78 (   2 unt;  32 nHn;  64 RR)
%            Number of literals    :  289 (   0 equ; 180 neg)
%            Maximal clause size   :   29 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   35 (  35 usr;   1 prp; 0-4 aty)
%            Number of functors    :   28 (  28 usr;  19 con; 0-3 aty)
%            Number of variables   :  132 (  29 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP165+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc63) ).

cnf(clause2,negated_conjecture,
    actual_world(skc19) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | frontseat(skc63,skc72) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | two(skc63,skc71) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | group(skc63,skc71) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | ssSkP0(skc71,skc63) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | old(skc63,skc70) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | dirty(skc63,skc70) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | white(skc63,skc70) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | chevy(skc63,skc70) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | barrel(skc63,skc66) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | present(skc63,skc66) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | event(skc63,skc66) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | hollywood_placename(skc63,skc68) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkC0
    | placename(skc63,skc68) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkC0
    | city(skc63,skc69) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkC0
    | street(skc63,skc67) ) ).

cnf(clause18,negated_conjecture,
    ( ssSkC0
    | lonely(skc63,skc67) ) ).

cnf(clause19,negated_conjecture,
    ( ssSkC0
    | group(skc63,skc65) ) ).

cnf(clause20,negated_conjecture,
    ( ssSkC0
    | group(skc63,skc64) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc22,skc19) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | group(skc19,skc22) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | two(skc19,skc22) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | chevy(skc19,skc27) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | white(skc19,skc27) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | dirty(skc19,skc27) ) ).

cnf(clause27,negated_conjecture,
    ( ~ ssSkC0
    | old(skc19,skc27) ) ).

cnf(clause28,negated_conjecture,
    ( ~ ssSkC0
    | event(skc19,skc23) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | present(skc19,skc23) ) ).

cnf(clause30,negated_conjecture,
    ( ~ ssSkC0
    | barrel(skc19,skc23) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | placename(skc19,skc25) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | hollywood_placename(skc19,skc25) ) ).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | city(skc19,skc26) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | lonely(skc19,skc24) ) ).

cnf(clause35,negated_conjecture,
    ( ~ ssSkC0
    | street(skc19,skc24) ) ).

cnf(clause36,negated_conjecture,
    ( ~ ssSkC0
    | frontseat(skc19,skc24) ) ).

cnf(clause37,negated_conjecture,
    ( ~ ssSkC0
    | group(skc19,skc20) ) ).

cnf(clause38,negated_conjecture,
    ( ~ ssSkC0
    | group(skc19,skc21) ) ).

cnf(clause39,negated_conjecture,
    ( ssSkC0
    | ssSkP1(skc72,skc71,skc63) ) ).

cnf(clause40,negated_conjecture,
    ( ssSkC0
    | agent(skc63,skc66,skc70) ) ).

cnf(clause41,negated_conjecture,
    ( ssSkC0
    | in(skc63,skc66,skc69) ) ).

cnf(clause42,negated_conjecture,
    ( ssSkC0
    | of(skc63,skc68,skc69) ) ).

cnf(clause43,negated_conjecture,
    ( ssSkC0
    | down(skc63,skc66,skc67) ) ).

cnf(clause44,negated_conjecture,
    ( ssSkC0
    | ssSkP2(skc65,skc64,skc63) ) ).

cnf(clause45,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc19,skc23,skc27) ) ).

cnf(clause46,negated_conjecture,
    ( ~ ssSkC0
    | of(skc19,skc25,skc26) ) ).

cnf(clause47,negated_conjecture,
    ( ~ ssSkC0
    | in(skc19,skc23,skc26) ) ).

cnf(clause48,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP1(skc24,skc22,skc19) ) ).

cnf(clause49,negated_conjecture,
    ( ~ ssSkC0
    | down(skc19,skc23,skc24) ) ).

cnf(clause50,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP2(skc21,skc20,skc19) ) ).

cnf(clause51,negated_conjecture,
    ( ssSkP0(U,V)
    | member(V,skf11(V,U),U) ) ).

cnf(clause52,negated_conjecture,
    ( ~ member(skc63,U,skc64)
    | ssSkC0
    | coat(skc63,U) ) ).

cnf(clause53,negated_conjecture,
    ( ~ member(skc63,U,skc64)
    | ssSkC0
    | black(skc63,U) ) ).

cnf(clause54,negated_conjecture,
    ( ~ member(skc63,U,skc64)
    | ssSkC0
    | cheap(skc63,U) ) ).

cnf(clause55,negated_conjecture,
    ( ~ member(skc19,U,skc20)
    | ~ ssSkC0
    | coat(skc19,U) ) ).

cnf(clause56,negated_conjecture,
    ( ~ member(skc19,U,skc20)
    | ~ ssSkC0
    | black(skc19,U) ) ).

cnf(clause57,negated_conjecture,
    ( ~ member(skc19,U,skc20)
    | ~ ssSkC0
    | cheap(skc19,U) ) ).

cnf(clause58,negated_conjecture,
    ( ssSkP1(U,V,W)
    | member(W,skf16(U,W,V),V) ) ).

cnf(clause59,negated_conjecture,
    ( ssSkP2(U,V,W)
    | member(W,skf21(U,W,X),U) ) ).

cnf(clause60,negated_conjecture,
    ( ssSkP2(U,V,W)
    | member(W,skf19(U,W,V),V) ) ).

cnf(clause61,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | fellow(U,V) ) ).

cnf(clause62,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(W,U)
    | young(U,V) ) ).

cnf(clause63,negated_conjecture,
    ( ~ young(U,skf11(U,V))
    | ~ fellow(U,skf11(U,V))
    | ssSkP0(W,U) ) ).

cnf(clause64,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | state(U,skf13(U,Y,Z)) ) ).

cnf(clause65,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | in(U,skf12(V,U,X),X) ) ).

cnf(clause66,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | be(U,skf13(U,Y,V),V,skf12(V,U,Y)) ) ).

cnf(clause67,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | wear(U,skf17(U,Z,X1)) ) ).

cnf(clause68,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | nonreflexive(U,skf17(U,Z,X1)) ) ).

cnf(clause69,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | present(U,skf17(U,Z,X1)) ) ).

cnf(clause70,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | event(U,skf17(U,Z,X1)) ) ).

cnf(clause71,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | agent(U,skf17(U,V,Z),V) ) ).

cnf(clause72,negated_conjecture,
    ( ~ in(U,V,W)
    | ~ be(U,X,skf16(W,U,Y),V)
    | ~ state(U,X)
    | ssSkP1(W,Z,U) ) ).

cnf(clause73,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ member(U,X,Y)
    | ~ ssSkP2(W,Y,U)
    | patient(U,skf17(U,V,X),X) ) ).

cnf(clause74,negated_conjecture,
    ( ~ wear(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf19(W,U,X))
    | ~ agent(U,V,skf21(W,U,X))
    | ~ event(U,V)
    | ssSkP2(W,Y,U) ) ).

cnf(clause75,negated_conjecture,
    ( ~ ssSkP0(U,V)
    | ~ group(V,U)
    | ~ two(V,U)
    | ~ chevy(V,W)
    | ~ white(V,W)
    | ~ dirty(V,W)
    | ~ old(V,W)
    | ~ agent(V,X,W)
    | ~ event(V,X)
    | ~ present(V,X)
    | ~ barrel(V,X)
    | ~ placename(V,Y)
    | ~ hollywood_placename(V,Y)
    | ~ of(V,Y,Z)
    | ~ city(V,Z)
    | ~ in(V,X,Z)
    | ~ ssSkP1(X1,U,V)
    | ~ down(V,X,X1)
    | ~ lonely(V,X1)
    | ~ street(V,X1)
    | ~ frontseat(V,X1)
    | ~ group(V,X2)
    | ~ ssSkP2(X3,X2,V)
    | ~ group(V,X3)
    | ~ actual_world(V)
    | ssSkC0
    | member(V,skf23(V,X2),X2) ) ).

cnf(clause76,negated_conjecture,
    ( ~ frontseat(U,V)
    | ~ ssSkP1(V,W,U)
    | ~ two(U,W)
    | ~ group(U,W)
    | ~ ssSkP0(W,U)
    | ~ agent(U,X,Y)
    | ~ old(U,Y)
    | ~ dirty(U,Y)
    | ~ white(U,Y)
    | ~ chevy(U,Y)
    | ~ barrel(U,X)
    | ~ present(U,X)
    | ~ event(U,X)
    | ~ hollywood_placename(U,Z)
    | ~ placename(U,Z)
    | ~ in(U,X,X1)
    | ~ city(U,X1)
    | ~ of(U,Z,X1)
    | ~ street(U,X2)
    | ~ lonely(U,X2)
    | ~ down(U,X,X2)
    | ~ ssSkP2(X3,X4,U)
    | ~ group(U,X3)
    | ~ group(U,X4)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf10(U,X4),X4) ) ).

cnf(clause77,negated_conjecture,
    ( ~ ssSkP0(U,V)
    | ~ group(V,U)
    | ~ two(V,U)
    | ~ chevy(V,W)
    | ~ white(V,W)
    | ~ dirty(V,W)
    | ~ old(V,W)
    | ~ agent(V,X,W)
    | ~ event(V,X)
    | ~ present(V,X)
    | ~ barrel(V,X)
    | ~ placename(V,Y)
    | ~ hollywood_placename(V,Y)
    | ~ of(V,Y,Z)
    | ~ city(V,Z)
    | ~ in(V,X,Z)
    | ~ ssSkP1(X1,U,V)
    | ~ down(V,X,X1)
    | ~ lonely(V,X1)
    | ~ street(V,X1)
    | ~ frontseat(V,X1)
    | ~ group(V,X2)
    | ~ cheap(V,skf23(V,X3))
    | ~ black(V,skf23(V,X3))
    | ~ coat(V,skf23(V,X3))
    | ~ ssSkP2(X4,X2,V)
    | ~ group(V,X4)
    | ~ actual_world(V)
    | ssSkC0 ) ).

cnf(clause78,negated_conjecture,
    ( ~ frontseat(U,V)
    | ~ ssSkP1(V,W,U)
    | ~ two(U,W)
    | ~ group(U,W)
    | ~ ssSkP0(W,U)
    | ~ agent(U,X,Y)
    | ~ old(U,Y)
    | ~ dirty(U,Y)
    | ~ white(U,Y)
    | ~ chevy(U,Y)
    | ~ barrel(U,X)
    | ~ present(U,X)
    | ~ event(U,X)
    | ~ hollywood_placename(U,Z)
    | ~ placename(U,Z)
    | ~ in(U,X,X1)
    | ~ city(U,X1)
    | ~ of(U,Z,X1)
    | ~ street(U,X2)
    | ~ lonely(U,X2)
    | ~ down(U,X,X2)
    | ~ ssSkP2(X3,X4,U)
    | ~ group(U,X3)
    | ~ cheap(U,skf10(U,X5))
    | ~ black(U,skf10(U,X5))
    | ~ coat(U,skf10(U,X5))
    | ~ group(U,X4)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
