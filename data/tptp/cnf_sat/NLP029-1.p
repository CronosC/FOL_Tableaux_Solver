%--------------------------------------------------------------------------
% File     : NLP029-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Three young guys, problem 4
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Three young guys sit at a table with hamburgers."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v6.3.0, 0.33 v6.2.0, 0.20 v6.1.0, 0.00 v5.4.0, 0.44 v5.3.0, 0.43 v5.0.0, 0.50 v4.1.0, 0.43 v4.0.0, 0.50 v3.5.0, 0.43 v3.4.0, 0.50 v3.3.0, 0.67 v3.2.0, 0.80 v3.1.0, 0.71 v2.7.0, 0.80 v2.6.0, 0.75 v2.5.0, 0.50 v2.4.0
% Syntax   : Number of clauses     :   46 (   2 unt;  12 nHn;  22 RR)
%            Number of literals    :  157 (   0 equ; 100 neg)
%            Maximal clause size   :    8 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   1 prp; 0-4 aty)
%            Number of functors    :   18 (  18 usr;   4 con; 0-4 aty)
%            Number of variables   :  175 (  74 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP029+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc63) ).

cnf(clause2,negated_conjecture,
    actual_world(skc4) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | group(skc63,skc64) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | three(skc63,skc64) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | ssSkP2(skc64,skc63) ) ).

cnf(clause6,negated_conjecture,
    ( ~ ssSkC0
    | group(skc4,skc5) ) ).

cnf(clause7,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP3(skc5,skc4) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkP2(U,V)
    | member(V,skf29(V,U),U) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkP3(U,V)
    | member(V,skf34(V,U),U) ) ).

cnf(clause10,negated_conjecture,
    ( ~ member(skc63,U,skc64)
    | ssSkC0
    | guy(skc63,U) ) ).

cnf(clause11,negated_conjecture,
    ( ~ member(skc63,U,skc64)
    | ssSkC0
    | young(skc63,U) ) ).

cnf(clause12,negated_conjecture,
    ( ~ member(skc4,U,skc5)
    | ~ ssSkC0
    | hamburger(skc4,U) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkP1(U,V,W)
    | member(W,skf23(U,W,V),V) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkP0(U,V,W,X)
    | member(X,skf18(W,X,Y,Z),W) ) ).

cnf(clause15,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(W,U)
    | table(U,skf26(U,X)) ) ).

cnf(clause16,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(W,U)
    | group(U,skf25(U,X)) ) ).

cnf(clause17,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP3(W,U)
    | three(U,skf32(U,X)) ) ).

cnf(clause18,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP3(W,U)
    | group(U,skf32(U,X)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP3(W,U)
    | ssSkP1(V,skf32(U,V),U) ) ).

cnf(clause20,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | table(U,skf20(U,Y,Z)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | sit(U,skf19(U,Y,Z)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | present(U,skf19(U,Y,Z)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | event(U,skf19(U,Y,Z)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | with(U,skf19(U,V,X),X) ) ).

cnf(clause25,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | agent(U,skf19(U,V,Y),V) ) ).

cnf(clause26,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | event(U,skf16(U,Z,X1,X2)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | present(U,skf16(U,Z,X1,X2)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | sit(U,skf16(U,Z,X1,X2)) ) ).

cnf(clause29,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(W,U)
    | ssSkP0(skf26(U,V),V,skf25(U,V),U) ) ).

cnf(clause30,negated_conjecture,
    ( ~ hamburger(U,skf37(U,V))
    | ~ group(U,W)
    | ~ ssSkP3(W,U)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause31,negated_conjecture,
    ( ~ group(U,V)
    | ~ ssSkP3(V,U)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf37(U,V),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | agent(U,skf16(U,V,X,Y),Y) ) ).

cnf(clause33,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | at(U,skf16(U,V,X,Z),X) ) ).

cnf(clause34,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | with(U,skf16(U,V,Z,X1),V) ) ).

cnf(clause35,negated_conjecture,
    ( ~ member(U,V,skf25(U,W))
    | ~ member(U,X,Y)
    | ~ ssSkP2(Y,U)
    | hamburger(U,V) ) ).

cnf(clause36,negated_conjecture,
    ( ~ member(U,V,skf32(U,W))
    | ~ member(U,X,Y)
    | ~ ssSkP3(Y,U)
    | young(U,V) ) ).

cnf(clause37,negated_conjecture,
    ( ~ member(U,V,skf32(U,W))
    | ~ member(U,X,Y)
    | ~ ssSkP3(Y,U)
    | guy(U,V) ) ).

cnf(clause38,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | at(U,skf19(U,Y,Z),skf20(U,Z,Y)) ) ).

cnf(clause39,negated_conjecture,
    ( ~ group(U,V)
    | ~ three(U,V)
    | ~ ssSkP2(V,U)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf15(U,V),V) ) ).

cnf(clause40,negated_conjecture,
    ( ~ group(U,V)
    | ~ three(U,V)
    | ~ ssSkP1(skf34(U,W),V,U)
    | ssSkP3(X,U)
    | member(U,skf35(U,V),V) ) ).

cnf(clause41,negated_conjecture,
    ( ~ group(U,V)
    | ~ ssSkP0(W,skf29(U,X),V,U)
    | ~ table(U,W)
    | ssSkP2(Y,U)
    | member(U,skf30(U,V),V) ) ).

cnf(clause42,negated_conjecture,
    ( ~ group(U,V)
    | ~ hamburger(U,skf30(U,W))
    | ~ ssSkP0(X,skf29(U,Y),V,U)
    | ~ table(U,X)
    | ssSkP2(Z,U) ) ).

cnf(clause43,negated_conjecture,
    ( ~ young(U,skf15(U,V))
    | ~ guy(U,skf15(U,V))
    | ~ group(U,W)
    | ~ three(U,W)
    | ~ ssSkP2(W,U)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause44,negated_conjecture,
    ( ~ young(U,skf35(U,V))
    | ~ guy(U,skf35(U,V))
    | ~ group(U,W)
    | ~ three(U,W)
    | ~ ssSkP1(skf34(U,X),W,U)
    | ssSkP3(Y,U) ) ).

cnf(clause45,negated_conjecture,
    ( ~ with(U,V,skf18(W,U,X,Y))
    | ~ at(U,V,X)
    | ~ sit(U,V)
    | ~ present(U,V)
    | ~ agent(U,V,Y)
    | ~ event(U,V)
    | ssSkP0(X,Y,W,U) ) ).

cnf(clause46,negated_conjecture,
    ( ~ event(U,V)
    | ~ agent(U,V,skf23(W,U,X))
    | ~ present(U,V)
    | ~ sit(U,V)
    | ~ with(U,V,W)
    | ~ at(U,V,Y)
    | ~ table(U,Y)
    | ssSkP1(W,Z,U) ) ).

%--------------------------------------------------------------------------
