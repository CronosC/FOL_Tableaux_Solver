%--------------------------------------------------------------------------
% File     : NLP117-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : An old dirty white Chevy, problem 4
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "An old dirty white chevy barrels down a lonely street in
%            hollywood."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v2.4.0
% Syntax   : Number of clauses     :   36 (   2 unt;  16 nHn;  36 RR)
%            Number of literals    :  102 (   0 equ;  51 neg)
%            Maximal clause size   :   18 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :   18 (  18 usr;   1 prp; 0-3 aty)
%            Number of functors    :   12 (  12 usr;  12 con; 0-0 aty)
%            Number of variables   :   12 (   0 sgn)
% SPC      : CNF_UNS_EPR_NEQ_NHN

% Comments : Created from NLP117+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc18) ).

cnf(clause2,negated_conjecture,
    actual_world(skc12) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | old(skc18,skc23) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | dirty(skc18,skc23) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | white(skc18,skc23) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | chevy(skc18,skc23) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | barrel(skc18,skc19) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | present(skc18,skc19) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | event(skc18,skc19) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | hollywood_placename(skc18,skc21) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | placename(skc18,skc21) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | city(skc18,skc22) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | street(skc18,skc20) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | lonely(skc18,skc20) ) ).

cnf(clause15,negated_conjecture,
    ( ~ ssSkC0
    | lonely(skc12,skc17) ) ).

cnf(clause16,negated_conjecture,
    ( ~ ssSkC0
    | street(skc12,skc17) ) ).

cnf(clause17,negated_conjecture,
    ( ~ ssSkC0
    | barrel(skc12,skc13) ) ).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | present(skc12,skc13) ) ).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | event(skc12,skc13) ) ).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | hollywood_placename(skc12,skc15) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | placename(skc12,skc15) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | city(skc12,skc16) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | chevy(skc12,skc14) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | white(skc12,skc14) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | dirty(skc12,skc14) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | old(skc12,skc14) ) ).

cnf(clause27,negated_conjecture,
    ( ssSkC0
    | agent(skc18,skc19,skc23) ) ).

cnf(clause28,negated_conjecture,
    ( ssSkC0
    | in(skc18,skc19,skc22) ) ).

cnf(clause29,negated_conjecture,
    ( ssSkC0
    | of(skc18,skc21,skc22) ) ).

cnf(clause30,negated_conjecture,
    ( ssSkC0
    | down(skc18,skc19,skc20) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | down(skc12,skc13,skc17) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | in(skc12,skc13,skc16) ) ).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | of(skc12,skc15,skc16) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc12,skc13,skc14) ) ).

cnf(clause35,negated_conjecture,
    ( ~ down(U,V,W)
    | ~ lonely(U,W)
    | ~ street(U,W)
    | ~ barrel(U,V)
    | ~ present(U,V)
    | ~ event(U,V)
    | ~ hollywood_placename(U,X)
    | ~ placename(U,X)
    | ~ in(U,V,Y)
    | ~ city(U,Y)
    | ~ of(U,X,Y)
    | ~ chevy(U,Z)
    | ~ white(U,Z)
    | ~ dirty(U,Z)
    | ~ old(U,Z)
    | ~ agent(U,V,Z)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause36,negated_conjecture,
    ( ~ agent(U,V,W)
    | ~ old(U,W)
    | ~ dirty(U,W)
    | ~ white(U,W)
    | ~ chevy(U,W)
    | ~ barrel(U,V)
    | ~ present(U,V)
    | ~ event(U,V)
    | ~ hollywood_placename(U,X)
    | ~ placename(U,X)
    | ~ in(U,V,Y)
    | ~ city(U,Y)
    | ~ of(U,X,Y)
    | ~ street(U,Z)
    | ~ lonely(U,Z)
    | ~ down(U,V,Z)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

%--------------------------------------------------------------------------
