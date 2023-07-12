%--------------------------------------------------------------------------
% File     : NLP028-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Three young guys, problem 3
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Three young guys sit at a table with hamburgers."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v6.3.0, 0.33 v6.2.0, 0.20 v6.1.0, 0.00 v5.4.0, 0.44 v5.3.0, 0.43 v5.0.0, 0.50 v4.1.0, 0.43 v4.0.0, 0.50 v3.5.0, 0.43 v3.4.0, 0.50 v3.3.0, 0.67 v3.2.0, 0.80 v3.1.0, 0.71 v2.7.0, 0.80 v2.6.0, 0.75 v2.5.0, 0.67 v2.4.0
% Syntax   : Number of clauses     :   46 (   2 unt;  13 nHn;  25 RR)
%            Number of literals    :  156 (   0 equ;  98 neg)
%            Maximal clause size   :    8 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   1 prp; 0-4 aty)
%            Number of functors    :   18 (  18 usr;   6 con; 0-4 aty)
%            Number of variables   :  198 (  90 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP028+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc65) ).

cnf(clause2,negated_conjecture,
    actual_world(skc6) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | three(skc65,skc66) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | group(skc65,skc66) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | table(skc65,skc67) ) ).

cnf(clause6,negated_conjecture,
    ( ~ ssSkC0
    | group(skc6,skc7) ) ).

cnf(clause7,negated_conjecture,
    ( ~ ssSkC0
    | table(skc6,skc8) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | ssSkP2(skc67,skc66,skc65) ) ).

cnf(clause9,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP3(skc8,skc7,skc6) ) ).

cnf(clause10,negated_conjecture,
    ( ~ member(skc65,U,skc66)
    | ssSkC0
    | guy(skc65,U) ) ).

cnf(clause11,negated_conjecture,
    ( ~ member(skc65,U,skc66)
    | ssSkC0
    | young(skc65,U) ) ).

cnf(clause12,negated_conjecture,
    ( ~ member(skc6,U,skc7)
    | ~ ssSkC0
    | hamburger(skc6,U) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkP2(U,V,W)
    | member(W,skf23(W,U,V),V) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkP3(U,V,W)
    | member(W,skf28(W,U,V),V) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkP0(U,V,W,X)
    | member(X,skf16(W,X,Y,Z),W) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkP1(U,V,W,X)
    | member(X,skf19(W,X,Y,Z),W) ) ).

cnf(clause17,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(X,W,U)
    | group(U,skf21(U,Y,Z)) ) ).

cnf(clause18,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP3(X,W,U)
    | three(U,skf26(U,Y,Z)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP3(X,W,U)
    | group(U,skf26(U,Y,Z)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | event(U,skf14(U,Z,X1,X2)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | present(U,skf14(U,Z,X1,X2)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | sit(U,skf14(U,Z,X1,X2)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | event(U,skf17(U,Z,X1,X2)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | present(U,skf17(U,Z,X1,X2)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | sit(U,skf17(U,Z,X1,X2)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(X,W,U)
    | ssSkP0(X,V,skf21(U,V,X),U) ) ).

cnf(clause27,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP3(X,W,U)
    | ssSkP1(V,X,skf26(U,X,V),U) ) ).

cnf(clause28,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | agent(U,skf14(U,V,X,Y),Y) ) ).

cnf(clause29,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | at(U,skf14(U,V,X,Z),X) ) ).

cnf(clause30,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | with(U,skf14(U,V,Z,X1),V) ) ).

cnf(clause31,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | agent(U,skf17(U,V,Z,X1),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | at(U,skf17(U,V,X,Y),Y) ) ).

cnf(clause33,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,Y,W,U)
    | with(U,skf17(U,V,X,Z),X) ) ).

cnf(clause34,negated_conjecture,
    ( ~ member(U,V,skf21(U,W,X))
    | ~ member(U,Y,Z)
    | ~ ssSkP2(X1,Z,U)
    | hamburger(U,V) ) ).

cnf(clause35,negated_conjecture,
    ( ~ member(U,V,skf26(U,W,X))
    | ~ member(U,Y,Z)
    | ~ ssSkP3(X1,Z,U)
    | young(U,V) ) ).

cnf(clause36,negated_conjecture,
    ( ~ member(U,V,skf26(U,W,X))
    | ~ member(U,Y,Z)
    | ~ ssSkP3(X1,Z,U)
    | guy(U,V) ) ).

cnf(clause37,negated_conjecture,
    ( ~ group(U,V)
    | ~ hamburger(U,skf31(U,W))
    | ~ ssSkP3(X,V,U)
    | ~ table(U,X)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause38,negated_conjecture,
    ( ~ group(U,V)
    | ~ ssSkP0(W,skf23(U,W,X),V,U)
    | ssSkP2(W,Y,U)
    | member(U,skf24(U,V),V) ) ).

cnf(clause39,negated_conjecture,
    ( ~ hamburger(U,skf24(U,V))
    | ~ group(U,W)
    | ~ ssSkP0(X,skf23(U,X,Y),W,U)
    | ssSkP2(X,Z,U) ) ).

cnf(clause40,negated_conjecture,
    ( ~ group(U,V)
    | ~ ssSkP3(W,V,U)
    | ~ table(U,W)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf31(U,V),V) ) ).

cnf(clause41,negated_conjecture,
    ( ~ group(U,V)
    | ~ three(U,V)
    | ~ ssSkP1(skf28(U,W,X),W,V,U)
    | ssSkP3(W,Y,U)
    | member(U,skf29(U,V),V) ) ).

cnf(clause42,negated_conjecture,
    ( ~ three(U,V)
    | ~ group(U,V)
    | ~ ssSkP2(W,V,U)
    | ~ table(U,W)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf13(U,V),V) ) ).

cnf(clause43,negated_conjecture,
    ( ~ young(U,skf29(U,V))
    | ~ guy(U,skf29(U,V))
    | ~ group(U,W)
    | ~ three(U,W)
    | ~ ssSkP1(skf28(U,X,Y),X,W,U)
    | ssSkP3(X,Z,U) ) ).

cnf(clause44,negated_conjecture,
    ( ~ three(U,V)
    | ~ group(U,V)
    | ~ young(U,skf13(U,W))
    | ~ guy(U,skf13(U,W))
    | ~ ssSkP2(X,V,U)
    | ~ table(U,X)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause45,negated_conjecture,
    ( ~ with(U,V,W)
    | ~ at(U,V,X)
    | ~ sit(U,V)
    | ~ present(U,V)
    | ~ agent(U,V,skf19(Y,U,W,X))
    | ~ event(U,V)
    | ssSkP1(W,X,Y,U) ) ).

cnf(clause46,negated_conjecture,
    ( ~ with(U,V,skf16(W,U,X,Y))
    | ~ at(U,V,X)
    | ~ sit(U,V)
    | ~ present(U,V)
    | ~ agent(U,V,Y)
    | ~ event(U,V)
    | ssSkP0(X,Y,W,U) ) ).

%--------------------------------------------------------------------------
