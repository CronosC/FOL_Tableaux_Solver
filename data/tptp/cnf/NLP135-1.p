%--------------------------------------------------------------------------
% File     : NLP135-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : An old dirty white Chevy, problem 22
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "An old dirty white chevy barrels down a lonely street in
%            hollywood. Two young fellas are in the front seat."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   60 (   2 unt;  25 nHn;  51 RR)
%            Number of literals    :  219 (   0 equ; 135 neg)
%            Maximal clause size   :   23 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   28 (  28 usr;   1 prp; 0-4 aty)
%            Number of functors    :   20 (  20 usr;  12 con; 0-2 aty)
%            Number of variables   :   72 (  11 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP135+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc42) ).

cnf(clause2,negated_conjecture,
    actual_world(skc12) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | city(skc42,skc46) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | chevy(skc42,skc46) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | white(skc42,skc46) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | dirty(skc42,skc46) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | old(skc42,skc46) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | placename(skc42,skc47) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | hollywood_placename(skc42,skc47) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | event(skc42,skc44) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | present(skc42,skc44) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | barrel(skc42,skc44) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | lonely(skc42,skc45) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | street(skc42,skc45) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkC0
    | group(skc42,skc43) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkC0
    | two(skc42,skc43) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkC0
    | ssSkP1(skc43,skc42) ) ).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | city(skc12,skc16) ) ).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | chevy(skc12,skc16) ) ).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | white(skc12,skc16) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | dirty(skc12,skc16) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | old(skc12,skc16) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | placename(skc12,skc17) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | hollywood_placename(skc12,skc17) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | event(skc12,skc14) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | present(skc12,skc14) ) ).

cnf(clause27,negated_conjecture,
    ( ~ ssSkC0
    | barrel(skc12,skc14) ) ).

cnf(clause28,negated_conjecture,
    ( ~ ssSkC0
    | lonely(skc12,skc15) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | street(skc12,skc15) ) ).

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
    | agent(skc42,skc44,skc46) ) ).

cnf(clause34,negated_conjecture,
    ( ssSkC0
    | in(skc42,skc44,skc46) ) ).

cnf(clause35,negated_conjecture,
    ( ssSkC0
    | of(skc42,skc47,skc46) ) ).

cnf(clause36,negated_conjecture,
    ( ssSkC0
    | down(skc42,skc44,skc45) ) ).

cnf(clause37,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc12,skc14,skc16) ) ).

cnf(clause38,negated_conjecture,
    ( ~ ssSkC0
    | in(skc12,skc14,skc16) ) ).

cnf(clause39,negated_conjecture,
    ( ~ ssSkC0
    | of(skc12,skc17,skc16) ) ).

cnf(clause40,negated_conjecture,
    ( ~ ssSkC0
    | down(skc12,skc14,skc15) ) ).

cnf(clause41,negated_conjecture,
    ( ssSkP0(U,V)
    | frontseat(V,skf14(V,W)) ) ).

cnf(clause42,negated_conjecture,
    ( ssSkP0(U,V)
    | member(V,skf14(V,U),U) ) ).

cnf(clause43,negated_conjecture,
    ( ssSkP1(U,V)
    | member(V,skf19(V,U),U) ) ).

cnf(clause44,negated_conjecture,
    ( ~ member(skc42,U,skc43)
    | ssSkC0
    | fellow(skc42,U) ) ).

cnf(clause45,negated_conjecture,
    ( ~ member(skc42,U,skc43)
    | ssSkC0
    | young(skc42,U) ) ).

cnf(clause46,negated_conjecture,
    ( ~ member(skc12,U,skc13)
    | ~ ssSkC0
    | fellow(skc12,U) ) ).

cnf(clause47,negated_conjecture,
    ( ~ member(skc12,U,skc13)
    | ~ ssSkC0
    | young(skc12,U) ) ).

cnf(clause48,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(W,U)
    | state(U,skf16(U,X)) ) ).

cnf(clause49,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(W,U)
    | frontseat(U,skf15(U,X)) ) ).

cnf(clause50,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(W,U)
    | in(U,skf15(U,X),skf15(U,X)) ) ).

cnf(clause51,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ frontseat(U,V)
    | ~ ssSkP0(W,U)
    | state(U,skf11(U,X)) ) ).

cnf(clause52,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(W,U)
    | be(U,skf16(U,V),V,skf15(U,V)) ) ).

cnf(clause53,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ frontseat(U,V)
    | ~ ssSkP0(W,U)
    | in(U,skf10(V,U),V) ) ).

cnf(clause54,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ frontseat(U,V)
    | ~ ssSkP0(W,U)
    | be(U,skf11(U,V),V,skf10(V,U)) ) ).

cnf(clause55,negated_conjecture,
    ( ~ in(U,V,skf14(U,W))
    | ~ be(U,X,skf14(U,W),V)
    | ~ state(U,X)
    | ssSkP0(Y,U) ) ).

cnf(clause56,negated_conjecture,
    ( ~ frontseat(U,V)
    | ~ in(U,V,V)
    | ~ be(U,W,skf19(U,X),V)
    | ~ state(U,W)
    | ssSkP1(Y,U) ) ).

cnf(clause57,negated_conjecture,
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
    | ssSkC0
    | member(U,skf21(U,Z),Z) ) ).

cnf(clause58,negated_conjecture,
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
    | ~ ssSkP1(Z,U)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf9(U,Z),Z) ) ).

cnf(clause59,negated_conjecture,
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
    | ~ young(U,skf21(U,Z))
    | ~ fellow(U,skf21(U,Z))
    | ~ group(U,X1)
    | ~ two(U,X1)
    | ~ ssSkP0(X1,U)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause60,negated_conjecture,
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
    | ~ young(U,skf9(U,Z))
    | ~ fellow(U,skf9(U,Z))
    | ~ group(U,X1)
    | ~ two(U,X1)
    | ~ ssSkP1(X1,U)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
