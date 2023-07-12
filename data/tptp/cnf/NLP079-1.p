%--------------------------------------------------------------------------
% File     : NLP079-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : A man comes out of the bathroom, problem 19
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
% Rating   : 0.14 v8.1.0, 0.00 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v4.0.0, 0.14 v3.4.0, 0.25 v3.3.0, 0.33 v3.2.0, 0.00 v3.1.0, 0.17 v2.7.0, 0.12 v2.6.0, 0.00 v2.5.0, 0.25 v2.4.0
% Syntax   : Number of clauses     :   51 (   2 unt;  20 nHn;  44 RR)
%            Number of literals    :  187 (   0 equ; 117 neg)
%            Maximal clause size   :   20 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   21 (  21 usr;   1 prp; 0-4 aty)
%            Number of functors    :   20 (  20 usr;  16 con; 0-4 aty)
%            Number of variables   :   97 (  36 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created from NLP079+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc42) ).

cnf(clause2,negated_conjecture,
    actual_world(skc16) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | six(skc42,skc47) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | group(skc42,skc47) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | cannon(skc42,skc48) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | male(skc42,skc49) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | man(skc42,skc49) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | revenge(skc42,skc46) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | male(skc42,skc45) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | scream(skc42,skc43) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | nonreflexive(skc42,skc43) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | present(skc42,skc43) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | event(skc42,skc43) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | cry(skc42,skc44) ) ).

cnf(clause15,negated_conjecture,
    ( ~ ssSkC0
    | six(skc16,skc21) ) ).

cnf(clause16,negated_conjecture,
    ( ~ ssSkC0
    | group(skc16,skc21) ) ).

cnf(clause17,negated_conjecture,
    ( ~ ssSkC0
    | cannon(skc16,skc22) ) ).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | male(skc16,skc23) ) ).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | man(skc16,skc23) ) ).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | cry(skc16,skc20) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | male(skc16,skc19) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | scream(skc16,skc17) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | nonreflexive(skc16,skc17) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | present(skc16,skc17) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | event(skc16,skc17) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | revenge(skc16,skc18) ) ).

cnf(clause27,negated_conjecture,
    ( ssSkC0
    | of(skc42,skc48,skc49) ) ).

cnf(clause28,negated_conjecture,
    ( ssSkC0
    | of(skc42,skc43,skc46) ) ).

cnf(clause29,negated_conjecture,
    ( ssSkC0
    | agent(skc42,skc43,skc45) ) ).

cnf(clause30,negated_conjecture,
    ( ssSkC0
    | patient(skc42,skc43,skc44) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | of(skc16,skc22,skc23) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | patient(skc16,skc17,skc20) ) ).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc16,skc17,skc19) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | of(skc16,skc17,skc18) ) ).

cnf(clause35,negated_conjecture,
    ( ssSkC0
    | ssSkP0(skc48,skc49,skc47,skc42) ) ).

cnf(clause36,negated_conjecture,
    ( ~ ssSkC0
    | ssSkP0(skc22,skc23,skc21,skc16) ) ).

cnf(clause37,negated_conjecture,
    ( ~ member(skc42,U,skc47)
    | ssSkC0
    | shot(skc42,U) ) ).

cnf(clause38,negated_conjecture,
    ( ~ member(skc16,U,skc21)
    | ~ ssSkC0
    | shot(skc16,U) ) ).

cnf(clause39,negated_conjecture,
    ( ssSkP0(U,V,W,X)
    | member(X,skf8(W,X,Y,Z),W) ) ).

cnf(clause40,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | event(U,skf6(U,Z,X1,X2)) ) ).

cnf(clause41,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | present(U,skf6(U,Z,X1,X2)) ) ).

cnf(clause42,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | nonreflexive(U,skf6(U,Z,X1,X2)) ) ).

cnf(clause43,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | fire(U,skf6(U,Z,X1,X2)) ) ).

cnf(clause44,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | agent(U,skf6(U,V,X,Y),Y) ) ).

cnf(clause45,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | patient(U,skf6(U,V,Z,X1),V) ) ).

cnf(clause46,negated_conjecture,
    ( ~ member(U,V,W)
    | ~ ssSkP0(X,Y,W,U)
    | from_loc(U,skf6(U,V,X,Z),X) ) ).

cnf(clause47,negated_conjecture,
    ( ~ from_loc(U,V,W)
    | ~ fire(U,V)
    | ~ nonreflexive(U,V)
    | ~ present(U,V)
    | ~ patient(U,V,skf8(X,U,W,Y))
    | ~ agent(U,V,Y)
    | ~ event(U,V)
    | ssSkP0(W,Y,X,U) ) ).

cnf(clause48,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf10(U,W))
    | ~ cannon(U,X)
    | ~ male(U,Y)
    | ~ man(U,Y)
    | ~ of(U,X,Y)
    | ~ ssSkP0(X,Y,V,U)
    | ~ patient(U,Z,X1)
    | ~ cry(U,X1)
    | ~ agent(U,Z,X2)
    | ~ male(U,X2)
    | ~ scream(U,Z)
    | ~ nonreflexive(U,Z)
    | ~ present(U,Z)
    | ~ event(U,Z)
    | ~ revenge(U,X3)
    | ~ of(U,Z,X3)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause49,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ cannon(U,W)
    | ~ male(U,X)
    | ~ man(U,X)
    | ~ of(U,W,X)
    | ~ ssSkP0(W,X,V,U)
    | ~ patient(U,Y,Z)
    | ~ cry(U,Z)
    | ~ agent(U,Y,X1)
    | ~ male(U,X1)
    | ~ scream(U,Y)
    | ~ nonreflexive(U,Y)
    | ~ present(U,Y)
    | ~ event(U,Y)
    | ~ revenge(U,X2)
    | ~ of(U,Y,X2)
    | ~ actual_world(U)
    | ssSkC0
    | member(U,skf10(U,V),V) ) ).

cnf(clause50,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ shot(U,skf5(U,W))
    | ~ cannon(U,X)
    | ~ male(U,Y)
    | ~ man(U,Y)
    | ~ of(U,X,Y)
    | ~ ssSkP0(X,Y,V,U)
    | ~ of(U,Z,X1)
    | ~ revenge(U,X1)
    | ~ agent(U,Z,X2)
    | ~ male(U,X2)
    | ~ scream(U,Z)
    | ~ nonreflexive(U,Z)
    | ~ present(U,Z)
    | ~ event(U,Z)
    | ~ cry(U,X3)
    | ~ patient(U,Z,X3)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause51,negated_conjecture,
    ( ~ six(U,V)
    | ~ group(U,V)
    | ~ cannon(U,W)
    | ~ male(U,X)
    | ~ man(U,X)
    | ~ of(U,W,X)
    | ~ ssSkP0(W,X,V,U)
    | ~ of(U,Y,Z)
    | ~ revenge(U,Z)
    | ~ agent(U,Y,X1)
    | ~ male(U,X1)
    | ~ scream(U,Y)
    | ~ nonreflexive(U,Y)
    | ~ present(U,Y)
    | ~ event(U,Y)
    | ~ cry(U,X2)
    | ~ patient(U,Y,X2)
    | ~ actual_world(U)
    | ~ ssSkC0
    | member(U,skf5(U,V),V) ) ).

%--------------------------------------------------------------------------
