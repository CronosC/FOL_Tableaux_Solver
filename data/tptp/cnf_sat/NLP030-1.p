%--------------------------------------------------------------------------
% File     : NLP030-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Three young guys, problem 5
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Three young guys sit at a table with hamburgers."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v5.5.0, 0.25 v5.4.0, 0.33 v5.3.0, 0.43 v5.0.0, 0.38 v4.1.0, 0.29 v4.0.0, 0.38 v3.5.0, 0.43 v3.4.0, 0.50 v3.3.0, 0.67 v3.2.0, 0.80 v3.1.0, 0.71 v2.7.0, 0.80 v2.6.0, 0.75 v2.5.0, 0.67 v2.4.0
% Syntax   : Number of clauses     :   46 (   2 unt;  12 nHn;  24 RR)
%            Number of literals    :  157 (   0 equ; 100 neg)
%            Maximal clause size   :    7 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   1 prp; 0-4 aty)
%            Number of functors    :   18 (  18 usr;   5 con; 0-4 aty)
%            Number of variables   :  194 (  88 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP030+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc65) ).

cnf(clause2,negated_conjecture,
    actual_world(skc5) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | group(skc65,skc66) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | three(skc65,skc66) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | ssSkP3(skc66,skc65) ) ).

cnf(clause6,negated_conjecture,
    ( ~ ssSkC0
    | group(skc5,skc6) ) ).

cnf(clause7,negated_conjecture,
    ( ~ ssSkC0
    | table(skc5,skc7) ) ).

cnf(clause8,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP2(skc7,skc6,skc5) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkP3(U,V)
    | member(V,skf31(V,U),U) ) ).

cnf(clause10,negated_conjecture,
    ( ~ member(skc65,U,skc66)
    | ssSkC0
    | guy(skc65,U) ) ).

cnf(clause11,negated_conjecture,
    ( ~ member(skc65,U,skc66)
    | ssSkC0
    | young(skc65,U) ) ).

cnf(clause12,negated_conjecture,
    ( ~ member(skc5,U,skc6)
    | ~ ssSkC0
    | hamburger(skc5,U) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkP2(U,V,W)
    | member(W,skf24(W,U,V),V) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkP0(U,V,W,X)
    | member(X,skf17(W,X,Y,Z),W) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkP1(U,V,W,X)
    | member(X,skf20(W,X,Y,Z),W) ) ).

cnf(clause16,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP3(W,U)
    | table(U,skf28(U,X)) ) ).

cnf(clause17,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP3(W,U)
    | group(U,skf27(U,X)) ) ).

cnf(clause18,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(X,W,U)
    | three(U,skf22(U,Y,Z)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(X,W,U)
    | group(U,skf22(U,Y,Z)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | event(U,skf15(U,Z,X1,X2)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | present(U,skf15(U,Z,X1,X2)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | sit(U,skf15(U,Z,X1,X2)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | event(U,skf18(U,Z,X1,X2)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | present(U,skf18(U,Z,X1,X2)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | sit(U,skf18(U,Z,X1,X2)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(X,W,U)
    | ssSkP1(V,X,skf22(U,X,V),U) ) ).

cnf(clause27,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP3(W,U)
    | ssSkP0(skf28(U,V),V,skf27(U,V),U) ) ).

cnf(clause28,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | agent(U,skf15(U,V,X,Y),Y) ) ).

cnf(clause29,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | at(U,skf15(U,V,X,Z),X) ) ).

cnf(clause30,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | with(U,skf15(U,V,Z,X1),V) ) ).

cnf(clause31,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | agent(U,skf18(U,V,Z,X1),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | at(U,skf18(U,V,X,Y),Y) ) ).

cnf(clause33,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | with(U,skf18(U,V,X,Z),X) ) ).

cnf(clause34,negated_conjecture,
    ( ~ member(U,V,skf27(U,W))
    | ~ member(U,X,Y)
    | ~ ssSkP3(Y,U)
    | hamburger(U,V) ) ).

cnf(clause35,negated_conjecture,
    ( ~ member(U,V,skf22(U,W,X))
    | ~ member(U,Y,Z)
    | ~ ssSkP2(X1,Z,U)
    | young(U,V) ) ).

cnf(clause36,negated_conjecture,
    ( ~ member(U,V,skf22(U,W,X))
    | ~ member(U,Y,Z)
    | ~ ssSkP2(X1,Z,U)
    | guy(U,V) ) ).

cnf(clause37,negated_conjecture,
    ( ~ group(U,V)
    | ~ hamburger(U,skf34(U,W))
    | ~ ssSkP2(X,V,U)
    | ~ table(U,X)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause38,negated_conjecture,
    ( ~ group(U,V)
    | ~ three(U,V)
    | ~ ssSkP3(V,U)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf14(U,V),V) ) ).

cnf(clause39,negated_conjecture,
    ( ~ group(U,V)
    | ~ ssSkP2(W,V,U)
    | ~ table(U,W)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf34(U,V),V) ) ).

cnf(clause40,negated_conjecture,
    ( ~ group(U,V)
    | ~ ssSkP0(W,skf31(U,X),V,U)
    | ~ table(U,W)
    | ssSkP3(Y,U)
    | member(U,skf32(U,V),V) ) ).

cnf(clause41,negated_conjecture,
    ( ~ group(U,V)
    | ~ hamburger(U,skf32(U,W))
    | ~ ssSkP0(X,skf31(U,Y),V,U)
    | ~ table(U,X)
    | ssSkP3(Z,U) ) ).

cnf(clause42,negated_conjecture,
    ( ~ group(U,V)
    | ~ three(U,V)
    | ~ ssSkP1(skf24(U,W,X),W,V,U)
    | ssSkP2(W,Y,U)
    | member(U,skf25(U,V),V) ) ).

cnf(clause43,negated_conjecture,
    ( ~ young(U,skf14(U,V))
    | ~ guy(U,skf14(U,V))
    | ~ group(U,W)
    | ~ three(U,W)
    | ~ ssSkP3(W,U)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause44,negated_conjecture,
    ( ~ young(U,skf25(U,V))
    | ~ guy(U,skf25(U,V))
    | ~ group(U,W)
    | ~ three(U,W)
    | ~ ssSkP1(skf24(U,X,Y),X,W,U)
    | ssSkP2(X,Z,U) ) ).

cnf(clause45,negated_conjecture,
    ( ~ with(U,V,skf17(W,U,X,Y))
    | ~ at(U,V,X)
    | ~ sit(U,V)
    | ~ present(U,V)
    | ~ agent(U,V,Y)
    | ~ event(U,V)
    | ssSkP0(X,Y,W,U) ) ).

cnf(clause46,negated_conjecture,
    ( ~ with(U,V,W)
    | ~ at(U,V,X)
    | ~ sit(U,V)
    | ~ present(U,V)
    | ~ agent(U,V,skf20(Y,U,W,X))
    | ~ event(U,V)
    | ssSkP1(W,X,Y,U) ) ).

%--------------------------------------------------------------------------
