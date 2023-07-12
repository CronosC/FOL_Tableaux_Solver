%--------------------------------------------------------------------------
% File     : NLP062-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : A man comes out of the bathroom, problem 4
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "A man comes out of the bathroom with a magnum in his hand.
%            The man fires six shots from his canon."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v5.4.0, 0.22 v5.3.0, 0.29 v5.0.0, 0.25 v4.1.0, 0.14 v4.0.0, 0.25 v3.5.0, 0.29 v3.4.0, 0.33 v3.2.0, 0.60 v3.1.0, 0.57 v2.7.0, 0.60 v2.6.0, 0.50 v2.5.0, 0.33 v2.4.0
% Syntax   : Number of clauses     :   40 (   2 unt;  11 nHn;  20 RR)
%            Number of literals    :  157 (   0 equ; 107 neg)
%            Maximal clause size   :   10 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   1 prp; 0-3 aty)
%            Number of functors    :   16 (  16 usr;   6 con; 0-4 aty)
%            Number of variables   :  166 (  74 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP062+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc60) ).

cnf(clause2,negated_conjecture,
    actual_world(skc6) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | six(skc60,skc61) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | group(skc60,skc61) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | male(skc60,skc62) ) ).

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
    | ssSkP0(skc61,skc62,skc60) ) ).

cnf(clause10,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP1(skc8,skc7,skc6) ) ).

cnf(clause11,negated_conjecture,
    ( ~ member(skc60,U,skc61)
    | ssSkC0
    | shot(skc60,U) ) ).

cnf(clause12,negated_conjecture,
    ( ~ member(skc6,U,skc7)
    | ~ ssSkC0
    | shot(skc6,U) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkP0(U,V,W)
    | cannon(W,skf19(W,X,Y)) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkP1(U,V,W)
    | man(W,skf27(W,X,Y)) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkP0(U,V,W)
    | member(W,skf16(U,W,X),U) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkP0(U,V,W)
    | of(W,skf19(W,V,X),V) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkP1(U,V,W)
    | member(W,skf24(V,W,X),V) ) ).

cnf(clause18,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | event(U,skf20(U,Z,X1,X2)) ) ).

cnf(clause19,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | present(U,skf20(U,Z,X1,X2)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | nonreflexive(U,skf20(U,Z,X1,X2)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | fire(U,skf20(U,Z,X1,X2)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | cannon(U,skf21(U,Z,X1,X2)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | of(U,skf21(U,Y,Z,X1),Y) ) ).

cnf(clause24,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | agent(U,skf20(U,X,Z,X1),X) ) ).

cnf(clause25,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | patient(U,skf20(U,X,V,Z),V) ) ).

cnf(clause26,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,X)
    | ~ of(U,X,Y)
    | ~ ssSkP0(W,Y,U)
    | fire(U,skf12(U,Z,X1)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,X)
    | ~ of(U,X,Y)
    | ~ ssSkP0(W,Y,U)
    | man(U,skf13(U,Z,X1)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,X)
    | ~ of(U,X,Y)
    | ~ ssSkP0(W,Y,U)
    | event(U,skf12(U,Z,X1)) ) ).

cnf(clause29,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,X)
    | ~ of(U,X,Y)
    | ~ ssSkP0(W,Y,U)
    | present(U,skf12(U,Z,X1)) ) ).

cnf(clause30,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,X)
    | ~ of(U,X,Y)
    | ~ ssSkP0(W,Y,U)
    | nonreflexive(U,skf12(U,Z,X1)) ) ).

cnf(clause31,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,X)
    | ~ of(U,X,Y)
    | ~ ssSkP0(W,Y,U)
    | from_loc(U,skf12(U,X,Z),X) ) ).

cnf(clause32,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(Y,W,U)
    | from_loc(U,skf20(U,X,V,Y),skf21(U,Y,V,X)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,X)
    | ~ of(U,X,Y)
    | ~ ssSkP0(W,Y,U)
    | patient(U,skf12(U,X,V),V) ) ).

cnf(clause34,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf29(U,W))
    | ~ ssSkP1(X,V,U)
    | ~ male(U,X)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause35,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ ssSkP1(W,V,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf29(U,V),V) ) ).

cnf(clause36,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf11(U,W))
    | ~ ssSkP0(V,X,U)
    | ~ male(U,X)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause37,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ ssSkP0(V,W,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf11(U,V),V) ) ).

cnf(clause38,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,X)
    | ~ of(U,X,Y)
    | ~ ssSkP0(W,Y,U)
    | agent(U,skf12(U,Z,X1),skf13(U,X1,Z)) ) ).

cnf(clause39,negated_conjecture,
    ( ~ event(U,V)
    | ~ patient(U,V,skf16(W,U,X))
    | ~ present(U,V)
    | ~ nonreflexive(U,V)
    | ~ fire(U,V)
    | ~ from_loc(U,V,skf19(U,X,W))
    | ~ agent(U,V,Y)
    | ~ man(U,Y)
    | ssSkP0(W,X,U) ) ).

cnf(clause40,negated_conjecture,
    ( ~ event(U,V)
    | ~ agent(U,V,skf27(U,W,X))
    | ~ patient(U,V,skf24(W,U,X))
    | ~ present(U,V)
    | ~ nonreflexive(U,V)
    | ~ fire(U,V)
    | ~ from_loc(U,V,Y)
    | ~ cannon(U,Y)
    | ~ of(U,Y,X)
    | ssSkP1(X,W,U) ) ).

%--------------------------------------------------------------------------
