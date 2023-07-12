%--------------------------------------------------------------------------
% File     : NLP059-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : A man comes out of the bathroom, problem 1
% Version  : [Bos00b] axioms.
% English  : Eliminating inconsistent interpretations in the statement
%            "A man comes out of the bathroom with a magnum in his hand.
%            The man fires six shots from his canon."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.5.0, 0.14 v3.4.0, 0.00 v3.2.0, 0.20 v3.1.0, 0.29 v2.7.0, 0.20 v2.6.0, 0.25 v2.5.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   40 (   2 unt;  13 nHn;  20 RR)
%            Number of literals    :  165 (   0 equ; 113 neg)
%            Maximal clause size   :    9 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   1 prp; 0-3 aty)
%            Number of functors    :   14 (  14 usr;   6 con; 0-3 aty)
%            Number of variables   :  140 (  40 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP059+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc50) ).

cnf(clause2,negated_conjecture,
    actual_world(skc6) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | six(skc50,skc51) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | group(skc50,skc51) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | male(skc50,skc52) ) ).

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
    | ssSkP1(skc51,skc52,skc50) ) ).

cnf(clause10,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc7,skc8,skc6) ) ).

cnf(clause11,negated_conjecture,
    ( ~ member(skc50,U,skc51)
    | ssSkC0
    | shot(skc50,U) ) ).

cnf(clause12,negated_conjecture,
    ( ~ member(skc6,U,skc7)
    | ~ ssSkC0
    | shot(skc6,U) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkP0(U,V,W)
    | cannon(W,skf12(W,X,Y)) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkP0(U,V,W)
    | man(W,skf14(W,X,Y)) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkP1(U,V,W)
    | cannon(W,skf19(W,X,Y)) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkP0(U,V,W)
    | of(W,skf12(W,V,X),V) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkP0(U,V,W)
    | member(W,skf12(W,V,U),U) ) ).

cnf(clause18,negated_conjecture,
    ( ssSkP1(U,V,W)
    | member(W,skf19(W,U,X),U) ) ).

cnf(clause19,negated_conjecture,
    ( ssSkP1(U,V,W)
    | of(W,skf19(W,U,V),V) ) ).

cnf(clause20,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,X)
    | ~ ssSkP1(W,X,U)
    | man(U,skf16(U,Y)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,X)
    | ~ ssSkP1(W,X,U)
    | fire(U,skf15(U,Y)) ) ).

cnf(clause22,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,X)
    | ~ ssSkP1(W,X,U)
    | nonreflexive(U,skf15(U,Y)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,X)
    | ~ ssSkP1(W,X,U)
    | present(U,skf15(U,Y)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,X)
    | ~ ssSkP1(W,X,U)
    | event(U,skf15(U,Y)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,X)
    | ~ ssSkP1(W,X,U)
    | patient(U,skf15(U,V),V) ) ).

cnf(clause26,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,X)
    | ~ ssSkP1(W,X,U)
    | from_loc(U,skf15(U,V),V) ) ).

cnf(clause27,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf21(U,W))
    | ~ ssSkP0(V,X,U)
    | ~ male(U,X)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause28,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ ssSkP0(V,W,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf21(U,V),V) ) ).

cnf(clause29,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,X)
    | ~ ssSkP1(W,X,U)
    | agent(U,skf15(U,Y),skf16(U,Y)) ) ).

cnf(clause30,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf9(U,W))
    | ~ ssSkP1(V,X,U)
    | ~ male(U,X)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause31,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ ssSkP1(V,W,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf9(U,V),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,X)
    | ~ man(U,Y)
    | ~ ssSkP0(X,W,U)
    | fire(U,skf10(U,Z,X1)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,X)
    | ~ man(U,Y)
    | ~ ssSkP0(X,W,U)
    | nonreflexive(U,skf10(U,Z,X1)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,X)
    | ~ man(U,Y)
    | ~ ssSkP0(X,W,U)
    | present(U,skf10(U,Z,X1)) ) ).

cnf(clause35,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,X)
    | ~ man(U,Y)
    | ~ ssSkP0(X,W,U)
    | event(U,skf10(U,Z,X1)) ) ).

cnf(clause36,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,X)
    | ~ man(U,Y)
    | ~ ssSkP0(X,W,U)
    | patient(U,skf10(U,Y,V),V) ) ).

cnf(clause37,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,X)
    | ~ man(U,Y)
    | ~ ssSkP0(X,W,U)
    | agent(U,skf10(U,Y,Z),Y) ) ).

cnf(clause38,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,X)
    | ~ man(U,Y)
    | ~ ssSkP0(X,W,U)
    | from_loc(U,skf10(U,Y,V),V) ) ).

cnf(clause39,negated_conjecture,
    ( ~ from_loc(U,V,skf12(U,W,X))
    | ~ fire(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf12(U,W,X))
    | ~ agent(U,V,skf14(U,X,W))
    | ~ event(U,V)
    | ssSkP0(Y,Z,U) ) ).

cnf(clause40,negated_conjecture,
    ( ~ event(U,V)
    | ~ patient(U,V,skf19(U,W,X))
    | ~ present(U,V)
    | ~ nonreflexive(U,V)
    | ~ fire(U,V)
    | ~ from_loc(U,V,skf19(U,W,X))
    | ~ agent(U,V,Y)
    | ~ man(U,Y)
    | ssSkP1(Z,X1,U) ) ).

%--------------------------------------------------------------------------
