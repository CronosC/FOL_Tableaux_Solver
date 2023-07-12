%--------------------------------------------------------------------------
% File     : NLP060-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : A man comes out of the bathroom, problem 2
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "A man comes out of the bathroom with a magnum in his hand.
%            The man fires six shots from his canon."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v5.4.0, 0.33 v5.3.0, 0.43 v5.0.0, 0.38 v4.1.0, 0.29 v4.0.0, 0.38 v3.5.0, 0.43 v3.4.0, 0.50 v3.2.0, 0.60 v3.1.0, 0.71 v2.7.0, 0.60 v2.6.0, 0.50 v2.5.0, 0.67 v2.4.0
% Syntax   : Number of clauses     :   40 (   2 unt;  12 nHn;  20 RR)
%            Number of literals    :  160 (   0 equ; 109 neg)
%            Maximal clause size   :   10 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   1 prp; 0-3 aty)
%            Number of functors    :   16 (  16 usr;   6 con; 0-4 aty)
%            Number of variables   :  174 (  85 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP060+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc61) ).

cnf(clause2,negated_conjecture,
    actual_world(skc6) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | six(skc61,skc62) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | group(skc61,skc62) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | male(skc61,skc63) ) ).

cnf(clause6,negated_conjecture,
    ( ~ ssSkC0
    | six(skc6,skc7) ) ).

cnf(clause7,negated_conjecture,
    ( ~ ssSkC0
    | group(skc6,skc7) ) ).

cnf(clause8,negated_conjecture,
    ( ~ ssSkC0
    | male(skc6,skc8) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | ssSkP1(skc63,skc62,skc61) ) ).

cnf(clause10,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc7,skc8,skc6) ) ).

cnf(clause11,negated_conjecture,
    ( ~ member(skc61,U,skc62)
    | ssSkC0
    | shot(skc61,U) ) ).

cnf(clause12,negated_conjecture,
    ( ~ member(skc6,U,skc7)
    | ~ ssSkC0
    | shot(skc6,U) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkP0(U,V,W)
    | cannon(W,skf16(W,X,Y)) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkP0(U,V,W)
    | man(W,skf18(W,X,Y)) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkP1(U,V,W)
    | man(W,skf26(W,X,Y)) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkP0(U,V,W)
    | member(W,skf14(U,W,X),U) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkP0(U,V,W)
    | of(W,skf16(W,V,X),V) ) ).

cnf(clause18,negated_conjecture,
    ( ssSkP1(U,V,W)
    | member(W,skf23(V,W,X),V) ) ).

cnf(clause19,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | event(U,skf19(U,Z,X1,X2)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | present(U,skf19(U,Z,X1,X2)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | nonreflexive(U,skf19(U,Z,X1,X2)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | fire(U,skf19(U,Z,X1,X2)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | cannon(U,skf20(U,Z,X1,X2)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | of(U,skf20(U,Y,Z,X1),Y) ) ).

cnf(clause25,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | agent(U,skf19(U,X,Z,X1),X) ) ).

cnf(clause26,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | patient(U,skf19(U,X,V,Z),V) ) ).

cnf(clause27,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | from_loc(U,skf19(U,X,V,Y),skf20(U,Y,V,X)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ ssSkP0(V,W,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf28(U,V),V) ) ).

cnf(clause29,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf28(U,W))
    | ~ ssSkP0(V,X,U)
    | ~ male(U,X)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause30,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ ssSkP1(W,V,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf11(U,V),V) ) ).

cnf(clause31,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf11(U,W))
    | ~ ssSkP1(X,V,U)
    | ~ male(U,X)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause32,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | nonreflexive(U,skf12(U,X1,X2,X3)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | present(U,skf12(U,X1,X2,X3)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | event(U,skf12(U,X1,X2,X3)) ) ).

cnf(clause35,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | fire(U,skf12(U,X1,X2,X3)) ) ).

cnf(clause36,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | agent(U,skf12(U,Z,X1,X2),Z) ) ).

cnf(clause37,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | from_loc(U,skf12(U,Z,X,X1),X) ) ).

cnf(clause38,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | patient(U,skf12(U,Z,X,V),V) ) ).

cnf(clause39,negated_conjecture,
    ( ~ from_loc(U,V,skf16(U,W,X))
    | ~ fire(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf14(X,U,W))
    | ~ agent(U,V,skf18(U,W,X))
    | ~ event(U,V)
    | ssSkP0(X,W,U) ) ).

cnf(clause40,negated_conjecture,
    ( ~ event(U,V)
    | ~ agent(U,V,skf26(U,W,X))
    | ~ patient(U,V,skf23(W,U,X))
    | ~ present(U,V)
    | ~ nonreflexive(U,V)
    | ~ fire(U,V)
    | ~ from_loc(U,V,Y)
    | ~ cannon(U,Y)
    | ~ of(U,Y,X)
    | ssSkP1(X,W,U) ) ).

%--------------------------------------------------------------------------
