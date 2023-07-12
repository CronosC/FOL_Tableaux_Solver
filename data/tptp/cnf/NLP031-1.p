%--------------------------------------------------------------------------
% File     : NLP031-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Three young guys, problem 6
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Three young guys sit at a table with hamburgers."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v5.4.0, 0.22 v5.3.0, 0.14 v5.0.0, 0.12 v4.1.0, 0.14 v4.0.0, 0.12 v3.5.0, 0.14 v3.4.0, 0.17 v3.2.0, 0.40 v3.1.0, 0.43 v2.7.0, 0.40 v2.6.0, 0.50 v2.4.0
% Syntax   : Number of clauses     :   38 (   2 unt;  11 nHn;  23 RR)
%            Number of literals    :  128 (   0 equ;  80 neg)
%            Maximal clause size   :    8 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   18 (  18 usr;   1 prp; 0-4 aty)
%            Number of functors    :   16 (  16 usr;   5 con; 0-4 aty)
%            Number of variables   :  129 (  52 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP031+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc50) ).

cnf(clause2,negated_conjecture,
    actual_world(skc5) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | group(skc50,skc51) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | three(skc50,skc51) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | ssSkP2(skc51,skc50) ) ).

cnf(clause6,negated_conjecture,
    ( ~ ssSkC0
    | three(skc5,skc6) ) ).

cnf(clause7,negated_conjecture,
    ( ~ ssSkC0
    | group(skc5,skc6) ) ).

cnf(clause8,negated_conjecture,
    ( ~ ssSkC0
    | table(skc5,skc7) ) ).

cnf(clause9,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP1(skc7,skc6,skc5) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkP2(U,V)
    | member(V,skf26(V,U),U) ) ).

cnf(clause11,negated_conjecture,
    ( ~ member(skc50,U,skc51)
    | ssSkC0
    | guy(skc50,U) ) ).

cnf(clause12,negated_conjecture,
    ( ~ member(skc50,U,skc51)
    | ssSkC0
    | young(skc50,U) ) ).

cnf(clause13,negated_conjecture,
    ( ~ member(skc5,U,skc6)
    | ~ ssSkC0
    | guy(skc5,U) ) ).

cnf(clause14,negated_conjecture,
    ( ~ member(skc5,U,skc6)
    | ~ ssSkC0
    | young(skc5,U) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkP1(U,V,W)
    | member(W,skf19(W,U,V),V) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkP0(U,V,W,X)
    | member(X,skf15(W,X,Y,Z),W) ) ).

cnf(clause17,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(W,U)
    | table(U,skf23(U,X)) ) ).

cnf(clause18,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(W,U)
    | group(U,skf22(U,X)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | group(U,skf17(U,Y,Z)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | event(U,skf13(U,Z,X1,X2)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | present(U,skf13(U,Z,X1,X2)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | sit(U,skf13(U,Z,X1,X2)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | ssSkP0(X,V,skf17(U,V,X),U) ) ).

cnf(clause24,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP2(W,U)
    | ssSkP0(skf23(U,V),V,skf22(U,V),U) ) ).

cnf(clause25,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | agent(U,skf13(U,V,X,Y),Y) ) ).

cnf(clause26,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | at(U,skf13(U,V,X,Z),X) ) ).

cnf(clause27,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | with(U,skf13(U,V,Z,X1),V) ) ).

cnf(clause28,negated_conjecture,
    ( ~ member(U,V,skf22(U,W))
    | ~ member(U,X,Y)
    | ~ ssSkP2(Y,U)
    | hamburger(U,V) ) ).

cnf(clause29,negated_conjecture,
    ( ~ member(U,V,skf17(U,W,X))
    | ~ member(U,Y,Z)
    | ~ ssSkP1(X1,Z,U)
    | hamburger(U,V) ) ).

cnf(clause30,negated_conjecture,
    ( ~ group(U,V)
    | ~ ssSkP0(W,skf19(U,W,X),V,U)
    | ssSkP1(W,Y,U)
    | member(U,skf20(U,V),V) ) ).

cnf(clause31,negated_conjecture,
    ( ~ hamburger(U,skf20(U,V))
    | ~ group(U,W)
    | ~ ssSkP0(X,skf19(U,X,Y),W,U)
    | ssSkP1(X,Z,U) ) ).

cnf(clause32,negated_conjecture,
    ( ~ group(U,V)
    | ~ three(U,V)
    | ~ ssSkP2(V,U)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf12(U,V),V) ) ).

cnf(clause33,negated_conjecture,
    ( ~ group(U,V)
    | ~ hamburger(U,skf27(U,W))
    | ~ ssSkP0(X,skf26(U,Y),V,U)
    | ~ table(U,X)
    | ssSkP2(Z,U) ) ).

cnf(clause34,negated_conjecture,
    ( ~ group(U,V)
    | ~ ssSkP0(W,skf26(U,X),V,U)
    | ~ table(U,W)
    | ssSkP2(Y,U)
    | member(U,skf27(U,V),V) ) ).

cnf(clause35,negated_conjecture,
    ( ~ three(U,V)
    | ~ group(U,V)
    | ~ ssSkP1(W,V,U)
    | ~ table(U,W)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf29(U,V),V) ) ).

cnf(clause36,negated_conjecture,
    ( ~ young(U,skf12(U,V))
    | ~ guy(U,skf12(U,V))
    | ~ group(U,W)
    | ~ three(U,W)
    | ~ ssSkP2(W,U)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause37,negated_conjecture,
    ( ~ three(U,V)
    | ~ group(U,V)
    | ~ young(U,skf29(U,W))
    | ~ guy(U,skf29(U,W))
    | ~ ssSkP1(X,V,U)
    | ~ table(U,X)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause38,negated_conjecture,
    ( ~ with(U,V,skf15(W,U,X,Y))
    | ~ at(U,V,X)
    | ~ sit(U,V)
    | ~ present(U,V)
    | ~ agent(U,V,Y)
    | ~ event(U,V)
    | ssSkP0(X,Y,W,U) ) ).

%--------------------------------------------------------------------------
