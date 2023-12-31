%--------------------------------------------------------------------------
% File     : NLP066-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : A man comes out of the bathroom, problem 8
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "A man comes out of the bathroom with a magnum in his hand.
%            The man fires six shots from his canon."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   40 (   2 unt;  14 nHn;  19 RR)
%            Number of literals    :  173 (   0 equ; 120 neg)
%            Maximal clause size   :    8 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   19 (  19 usr;   1 prp; 0-3 aty)
%            Number of functors    :   12 (  12 usr;   4 con; 0-3 aty)
%            Number of variables   :  118 (  37 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP066+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc48) ).

cnf(clause2,negated_conjecture,
    actual_world(skc4) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | group(skc48,skc49) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | six(skc48,skc49) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | ssSkP0(skc49,skc48) ) ).

cnf(clause6,negated_conjecture,
    ( ~ ssSkC0
    | group(skc4,skc5) ) ).

cnf(clause7,negated_conjecture,
    ( ~ ssSkC0
    | six(skc4,skc5) ) ).

cnf(clause8,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP1(skc5,skc4) ) ).

cnf(clause9,negated_conjecture,
    ( ~ ssSkC0
    | male(skc4,skc5) ) ).

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
    | cannon(V,skf17(V,W)) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkP1(U,V)
    | man(V,skf19(V,W)) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkP0(U,V)
    | member(V,skf12(V,U),U) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkP1(U,V)
    | of(V,skf17(V,U),U) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkP1(U,V)
    | member(V,skf17(V,U),U) ) ).

cnf(clause18,negated_conjecture,
    ( ~ member(skc48,U,skc49)
    | ssSkC0
    | shot(skc48,U) ) ).

cnf(clause19,negated_conjecture,
    ( ~ member(skc4,U,skc5)
    | ~ ssSkC0
    | shot(skc4,U) ) ).

cnf(clause20,negated_conjecture,
    ( ssSkP0(U,V)
    | of(V,skf12(V,W),skf14(V,W)) ) ).

cnf(clause21,negated_conjecture,
    ( ~ shot(U,skf9(U,V))
    | ~ group(U,W)
    | ~ six(U,W)
    | ~ ssSkP0(W,U)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause22,negated_conjecture,
    ( ~ group(U,V)
    | ~ six(U,V)
    | ~ ssSkP0(V,U)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf9(U,V),V) ) ).

cnf(clause23,negated_conjecture,
    ( ~ shot(U,skf21(U,V))
    | ~ group(U,W)
    | ~ six(U,W)
    | ~ ssSkP1(W,U)
    | ~ male(U,W)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause24,negated_conjecture,
    ( ~ group(U,V)
    | ~ six(U,V)
    | ~ ssSkP1(V,U)
    | ~ male(U,V)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf21(U,V),V) ) ).

cnf(clause25,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(W,U)
    | fire(U,skf15(U,Y,Z)) ) ).

cnf(clause26,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(W,U)
    | nonreflexive(U,skf15(U,Y,Z)) ) ).

cnf(clause27,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(W,U)
    | present(U,skf15(U,Y,Z)) ) ).

cnf(clause28,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(W,U)
    | event(U,skf15(U,Y,Z)) ) ).

cnf(clause29,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(W,U)
    | agent(U,skf15(U,X,Y),X) ) ).

cnf(clause30,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(W,U)
    | from_loc(U,skf15(U,X,V),V) ) ).

cnf(clause31,negated_conjecture,
    ( ~ of(U,V,W)
    | ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ man(U,X)
    | ~ ssSkP1(W,U)
    | patient(U,skf15(U,X,V),V) ) ).

cnf(clause32,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | fire(U,skf10(U,Y,Z)) ) ).

cnf(clause33,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | event(U,skf10(U,Y,Z)) ) ).

cnf(clause34,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | present(U,skf10(U,Y,Z)) ) ).

cnf(clause35,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | nonreflexive(U,skf10(U,Y,Z)) ) ).

cnf(clause36,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | agent(U,skf10(U,X,Y),X) ) ).

cnf(clause37,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | patient(U,skf10(U,X,V),V) ) ).

cnf(clause38,negated_conjecture,
    ( ~ cannon(U,V)
    | ~ member(U,V,W)
    | ~ of(U,V,X)
    | ~ man(U,X)
    | ~ male(U,X)
    | ~ ssSkP0(W,U)
    | from_loc(U,skf10(U,X,V),V) ) ).

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
    ( ~ from_loc(U,V,skf17(U,W))
    | ~ fire(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf17(U,W))
    | ~ agent(U,V,skf19(U,W))
    | ~ event(U,V)
    | ssSkP1(X,U) ) ).

%--------------------------------------------------------------------------
