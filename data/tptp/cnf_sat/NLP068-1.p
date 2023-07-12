%--------------------------------------------------------------------------
% File     : NLP068-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : A man comes out of the bathroom, problem 9
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "A man comes out of the bathroom with a magnum in his hand.
%            The man fires six shots from his canon."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.5.0, 0.14 v3.4.0, 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   40 (   2 unt;  14 nHn;  19 RR)
%            Number of literals    :  170 (   0 equ; 117 neg)
%            Maximal clause size   :    9 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   1 prp; 0-3 aty)
%            Number of functors    :   12 (  12 usr;   4 con; 0-3 aty)
%            Number of variables   :  109 (  27 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP068+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc47) ).

cnf(clause2,negated_conjecture,
    actual_world(skc4) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | group(skc47,skc48) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | six(skc47,skc48) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | ssSkP1(skc48,skc47) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | male(skc47,skc48) ) ).

cnf(clause7,negated_conjecture,
    ( ~ ssSkC0
    | group(skc4,skc5) ) ).

cnf(clause8,negated_conjecture,
    ( ~ ssSkC0
    | six(skc4,skc5) ) ).

cnf(clause9,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc5,skc4) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkP0(U,V)
    | cannon(V,skf12(V,W)) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkP0(U,V)
    | man(V,skf14(V,W)) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkP0(U,V)
    | male(V,skf14(V,W)) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkP1(U,V)
    | cannon(V,skf19(V,W)) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkP0(U,V)
    | member(V,skf12(V,U),U) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkP1(U,V)
    | member(V,skf19(V,U),U) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkP1(U,V)
    | of(V,skf19(V,U),U) ) ).

cnf(clause17,negated_conjecture,
    ( ~ member(skc47,U,skc48)
    | ssSkC0
    | shot(skc47,U) ) ).

cnf(clause18,negated_conjecture,
    ( ~ member(skc4,U,skc5)
    | ~ ssSkC0
    | shot(skc4,U) ) ).

cnf(clause19,negated_conjecture,
    ( ssSkP0(U,V)
    | of(V,skf12(V,W),skf14(V,W)) ) ).

cnf(clause20,negated_conjecture,
    ( ~ shot(U,skf21(U,V))
    | ~ group(U,W)
    | ~ six(U,W)
    | ~ ssSkP0(W,U)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause21,negated_conjecture,
    ( ~ group(U,V)
    | ~ six(U,V)
    | ~ ssSkP0(V,U)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf21(U,V),V) ) ).

cnf(clause22,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,W)
    | ~ ssSkP1(W,U)
    | nonreflexive(U,skf15(U,X)) ) ).

cnf(clause23,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,W)
    | ~ ssSkP1(W,U)
    | present(U,skf15(U,X)) ) ).

cnf(clause24,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,W)
    | ~ ssSkP1(W,U)
    | event(U,skf15(U,X)) ) ).

cnf(clause25,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,W)
    | ~ ssSkP1(W,U)
    | man(U,skf16(U,X)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,W)
    | ~ ssSkP1(W,U)
    | fire(U,skf15(U,X)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,W)
    | ~ ssSkP1(W,U)
    | patient(U,skf15(U,V),V) ) ).

cnf(clause28,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,W)
    | ~ ssSkP1(W,U)
    | from_loc(U,skf15(U,V),V) ) ).

cnf(clause29,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ cannon(U,V)
    | ~ of(U,V,W)
    | ~ ssSkP1(W,U)
    | agent(U,skf15(U,X),skf16(U,X)) ) ).

cnf(clause30,negated_conjecture,
    ( ~ shot(U,skf9(U,V))
    | ~ group(U,W)
    | ~ six(U,W)
    | ~ ssSkP1(W,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause31,negated_conjecture,
    ( ~ group(U,V)
    | ~ six(U,V)
    | ~ ssSkP1(V,U)
    | ~ male(U,V)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf9(U,V),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | event(U,skf10(U,Y,Z)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | present(U,skf10(U,Y,Z)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | nonreflexive(U,skf10(U,Y,Z)) ) ).

cnf(clause35,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | fire(U,skf10(U,Y,Z)) ) ).

cnf(clause36,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | patient(U,skf10(U,X,V),V) ) ).

cnf(clause37,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | from_loc(U,skf10(U,X,V),V) ) ).

cnf(clause38,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | agent(U,skf10(U,X,Y),X) ) ).

cnf(clause39,negated_conjecture,
    ( ~ from_loc(U,V,skf12(U,W))
    | ~ fire(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf12(U,W))
    | ~ agent(U,V,skf14(U,W))
    | ~ event(U,V)
    | ssSkP0(X,U) ) ).

cnf(clause40,negated_conjecture,
    ( ~ event(U,V)
    | ~ patient(U,V,skf19(U,W))
    | ~ present(U,V)
    | ~ nonreflexive(U,V)
    | ~ fire(U,V)
    | ~ from_loc(U,V,skf19(U,W))
    | ~ agent(U,V,X)
    | ~ man(U,X)
    | ssSkP1(Y,U) ) ).

%--------------------------------------------------------------------------
