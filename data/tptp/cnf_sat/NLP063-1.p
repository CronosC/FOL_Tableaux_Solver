%--------------------------------------------------------------------------
% File     : NLP063-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : A man comes out of the bathroom, problem 5
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "A man comes out of the bathroom with a magnum in his hand.
%            The man fires six shots from his canon."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v5.4.0, 0.33 v5.3.0, 0.29 v5.0.0, 0.25 v4.1.0, 0.29 v4.0.0, 0.25 v3.5.0, 0.29 v3.4.0, 0.33 v3.2.0, 0.40 v3.1.0, 0.57 v2.7.0, 0.40 v2.6.0, 0.50 v2.5.0, 0.17 v2.4.0
% Syntax   : Number of clauses     :   40 (   2 unt;  11 nHn;  19 RR)
%            Number of literals    :  153 (   0 equ; 103 neg)
%            Maximal clause size   :   11 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   1 prp; 0-3 aty)
%            Number of functors    :   16 (  16 usr;   6 con; 0-4 aty)
%            Number of variables   :  161 (  71 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP063+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc59) ).

cnf(clause2,negated_conjecture,
    actual_world(skc6) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | six(skc59,skc60) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | group(skc59,skc60) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | male(skc59,skc61) ) ).

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
    | ssSkP1(skc61,skc60,skc59) ) ).

cnf(clause10,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc7,skc8,skc6) ) ).

cnf(clause11,negated_conjecture,
    ( ~ member(skc59,U,skc60)
    | ssSkC0
    | shot(skc59,U) ) ).

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
    ( ssSkP0(U,V,W)
    | member(W,skf14(U,W,X),U) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkP0(U,V,W)
    | of(W,skf16(W,V,X),V) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkP1(U,V,W)
    | member(W,skf25(U,W,V),V) ) ).

cnf(clause18,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | cannon(U,skf21(U,Y,Z)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | event(U,skf19(U,Y,Z)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | present(U,skf19(U,Y,Z)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | nonreflexive(U,skf19(U,Y,Z)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | fire(U,skf19(U,Y,Z)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | man(U,skf20(U,Y,Z)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | of(U,skf21(U,X,Y),X) ) ).

cnf(clause25,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | patient(U,skf19(U,V,Y),V) ) ).

cnf(clause26,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | from_loc(U,skf19(U,V,X),skf21(U,X,V)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP1(X,W,U)
    | agent(U,skf19(U,Y,Z),skf20(U,Z,Y)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf27(U,W))
    | ~ ssSkP0(V,X,U)
    | ~ male(U,X)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause29,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ ssSkP0(V,W,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf27(U,V),V) ) ).

cnf(clause30,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf11(U,W))
    | ~ ssSkP1(X,V,U)
    | ~ male(U,X)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause31,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ ssSkP1(W,V,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf11(U,V),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | present(U,skf12(U,X1,X2,X3)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | event(U,skf12(U,X1,X2,X3)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | fire(U,skf12(U,X1,X2,X3)) ) ).

cnf(clause35,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | nonreflexive(U,skf12(U,X1,X2,X3)) ) ).

cnf(clause36,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | patient(U,skf12(U,Z,X,V),V) ) ).

cnf(clause37,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | agent(U,skf12(U,Z,X1,X2),Z) ) ).

cnf(clause38,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ of(U,X,Y)
    | ~ cannon(U,X)
    | ~ man(U,Z)
    | ~ ssSkP0(W,Y,U)
    | from_loc(U,skf12(U,Z,X,X1),X) ) ).

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
    ( ~ agent(U,V,W)
    | ~ man(U,W)
    | ~ fire(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf25(X,U,Y))
    | ~ event(U,V)
    | ~ of(U,Z,X)
    | ~ cannon(U,Z)
    | ~ from_loc(U,V,Z)
    | ssSkP1(X,X1,U) ) ).

%--------------------------------------------------------------------------
