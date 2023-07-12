%--------------------------------------------------------------------------
% File     : NLP081-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : A man comes out of the bathroom, problem 21
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "A man comes out of the bathroom with a magnum in his hand.
%            The man fires six shots from his canon. He screams a cry of
%            revenge."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.1.0, 0.17 v7.0.0, 0.25 v6.3.0, 0.14 v6.2.0, 0.00 v4.0.0, 0.14 v3.4.0, 0.25 v3.3.0, 0.33 v3.2.0, 0.00 v3.1.0, 0.17 v2.7.0, 0.12 v2.6.0, 0.00 v2.5.0, 0.25 v2.4.0
% Syntax   : Number of clauses     :   49 (   2 unt;  19 nHn;  42 RR)
%            Number of literals    :  179 (   0 equ; 112 neg)
%            Maximal clause size   :   19 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   21 (  21 usr;   1 prp; 0-4 aty)
%            Number of functors    :   18 (  18 usr;  14 con; 0-4 aty)
%            Number of variables   :   93 (  36 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created from NLP081+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc39) ).

cnf(clause2,negated_conjecture,
    actual_world(skc14) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | revenge(skc39,skc45) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | event(skc39,skc40) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | present(skc39,skc40) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | nonreflexive(skc39,skc40) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | scream(skc39,skc40) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | group(skc39,skc42) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | six(skc39,skc42) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | cannon(skc39,skc43) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | man(skc39,skc44) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | male(skc39,skc44) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | cry(skc39,skc41) ) ).

cnf(clause14,negated_conjecture,
    ( ~ ssSkC0
    | cry(skc14,skc20) ) ).

cnf(clause15,negated_conjecture,
    ( ~ ssSkC0
    | event(skc14,skc15) ) ).

cnf(clause16,negated_conjecture,
    ( ~ ssSkC0
    | present(skc14,skc15) ) ).

cnf(clause17,negated_conjecture,
    ( ~ ssSkC0
    | nonreflexive(skc14,skc15) ) ).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | scream(skc14,skc15) ) ).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | group(skc14,skc17) ) ).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | six(skc14,skc17) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | cannon(skc14,skc18) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | man(skc14,skc19) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | male(skc14,skc19) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | revenge(skc14,skc16) ) ).

cnf(clause25,negated_conjecture,
    ( ssSkC0
    | of(skc39,skc40,skc45) ) ).

cnf(clause26,negated_conjecture,
    ( ssSkC0
    | agent(skc39,skc40,skc44) ) ).

cnf(clause27,negated_conjecture,
    ( ssSkC0
    | of(skc39,skc43,skc44) ) ).

cnf(clause28,negated_conjecture,
    ( ssSkC0
    | patient(skc39,skc40,skc41) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | patient(skc14,skc15,skc20) ) ).

cnf(clause30,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc14,skc15,skc19) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | of(skc14,skc18,skc19) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | of(skc14,skc15,skc16) ) ).

cnf(clause33,negated_conjecture,
    ( ssSkC0
    | ssSkP0(skc43,skc44,skc42,skc39) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc18,skc19,skc17,skc14) ) ).

cnf(clause35,negated_conjecture,
    ( ~ member(skc39,U,skc42)
    | ssSkC0
    | shot(skc39,U) ) ).

cnf(clause36,negated_conjecture,
    ( ~ member(skc14,U,skc17)
    | ~ ssSkC0
    | shot(skc14,U) ) ).

cnf(clause37,negated_conjecture,
    ( ssSkP0(U,V,W,X)
    | member(X,skf9(W,X,Y,Z),W) ) ).

cnf(clause38,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | event(U,skf7(U,Z,X1,X2)) ) ).

cnf(clause39,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | present(U,skf7(U,Z,X1,X2)) ) ).

cnf(clause40,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | nonreflexive(U,skf7(U,Z,X1,X2)) ) ).

cnf(clause41,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | fire(U,skf7(U,Z,X1,X2)) ) ).

cnf(clause42,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | agent(U,skf7(U,V,X,Y),Y) ) ).

cnf(clause43,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | patient(U,skf7(U,V,Z,X1),V) ) ).

cnf(clause44,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | from_loc(U,skf7(U,V,X,Z),X) ) ).

cnf(clause45,negated_conjecture,
    ( ~ from_loc(U,V,W)
    | ~ fire(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf9(X,U,W,Y))
    | ~ agent(U,V,Y)
    | ~ event(U,V)
    | ssSkP0(W,Y,X,U) ) ).

cnf(clause46,negated_conjecture,
    ( ~ cry(U,V)
    | ~ patient(U,W,V)
    | ~ event(U,W)
    | ~ present(U,W)
    | ~ nonreflexive(U,W)
    | ~ scream(U,W)
    | ~ group(U,X)
    | ~ six(U,X)
    | ~ cannon(U,Y)
    | ~ agent(U,W,Z)
    | ~ ssSkP0(Y,Z,X,U)
    | ~ of(U,Y,Z)
    | ~ man(U,Z)
    | ~ male(U,Z)
    | ~ of(U,W,X1)
    | ~ revenge(U,X1)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf12(U,X),X) ) ).

cnf(clause47,negated_conjecture,
    ( ~ cry(U,V)
    | ~ patient(U,W,V)
    | ~ event(U,W)
    | ~ present(U,W)
    | ~ nonreflexive(U,W)
    | ~ scream(U,W)
    | ~ shot(U,skf12(U,X))
    | ~ group(U,Y)
    | ~ six(U,Y)
    | ~ cannon(U,Z)
    | ~ agent(U,W,X1)
    | ~ ssSkP0(Z,X1,Y,U)
    | ~ of(U,Z,X1)
    | ~ man(U,X1)
    | ~ male(U,X1)
    | ~ of(U,W,X2)
    | ~ revenge(U,X2)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause48,negated_conjecture,
    ( ~ revenge(U,V)
    | ~ of(U,W,V)
    | ~ event(U,W)
    | ~ present(U,W)
    | ~ nonreflexive(U,W)
    | ~ scream(U,W)
    | ~ group(U,X)
    | ~ six(U,X)
    | ~ cannon(U,Y)
    | ~ agent(U,W,Z)
    | ~ ssSkP0(Y,Z,X,U)
    | ~ of(U,Y,Z)
    | ~ man(U,Z)
    | ~ male(U,Z)
    | ~ patient(U,W,X1)
    | ~ cry(U,X1)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf6(U,X),X) ) ).

cnf(clause49,negated_conjecture,
    ( ~ revenge(U,V)
    | ~ of(U,W,V)
    | ~ event(U,W)
    | ~ present(U,W)
    | ~ nonreflexive(U,W)
    | ~ scream(U,W)
    | ~ shot(U,skf6(U,X))
    | ~ group(U,Y)
    | ~ six(U,Y)
    | ~ cannon(U,Z)
    | ~ agent(U,W,X1)
    | ~ ssSkP0(Z,X1,Y,U)
    | ~ of(U,Z,X1)
    | ~ man(U,X1)
    | ~ male(U,X1)
    | ~ patient(U,W,X2)
    | ~ cry(U,X2)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
