%--------------------------------------------------------------------------
% File     : NLP222-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Vincent believes that every man smokes, problem 3
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Vincent believes that every man smokes. Jules is a man."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v6.3.0, 0.33 v6.2.0, 0.20 v6.1.0, 0.00 v5.0.0, 0.12 v4.1.0, 0.14 v4.0.0, 0.12 v3.5.0, 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0, 0.17 v2.4.0
% Syntax   : Number of clauses     :   49 (   2 unt;  22 nHn;  43 RR)
%            Number of literals    :  184 (   0 equ; 114 neg)
%            Maximal clause size   :   24 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   17 (  17 usr;   1 prp; 0-4 aty)
%            Number of functors    :   21 (  21 usr;  17 con; 0-1 aty)
%            Number of variables   :   50 (  12 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP222+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc29) ).

cnf(clause2,negated_conjecture,
    actual_world(skc17) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | proposition(skc29,skc33) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | accessible_world(skc29,skc33) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | think_believe_consider(skc29,skc34) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | present(skc29,skc34) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | event(skc29,skc34) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | vincent_forename(skc29,skc35) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | forename(skc29,skc35) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | man(skc29,skc36) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | state(skc29,skc30) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | man(skc29,skc31) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | forename(skc29,skc32) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | jules_forename(skc29,skc32) ) ).

cnf(clause15,negated_conjecture,
    ( ~ ssSkC0
    | proposition(skc17,skc22) ) ).

cnf(clause16,negated_conjecture,
    ( ~ ssSkC0
    | accessible_world(skc17,skc22) ) ).

cnf(clause17,negated_conjecture,
    ( ~ ssSkC0
    | think_believe_consider(skc17,skc23) ) ).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | present(skc17,skc23) ) ).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | event(skc17,skc23) ) ).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | vincent_forename(skc17,skc24) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc17,skc24) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | man(skc17,skc25) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | state(skc17,skc18) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | man(skc17,skc19) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | jules_forename(skc17,skc20) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc17,skc20) ) ).

cnf(clause27,negated_conjecture,
    ( ~ ssSkC0
    | man(skc17,skc21) ) ).

cnf(clause28,negated_conjecture,
    ( ssSkC0
    | theme(skc29,skc34,skc33) ) ).

cnf(clause29,negated_conjecture,
    ( ssSkC0
    | agent(skc29,skc34,skc36) ) ).

cnf(clause30,negated_conjecture,
    ( ssSkC0
    | of(skc29,skc35,skc36) ) ).

cnf(clause31,negated_conjecture,
    ( ssSkC0
    | of(skc29,skc32,skc31) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | theme(skc17,skc23,skc22) ) ).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc17,skc23,skc25) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | of(skc17,skc24,skc25) ) ).

cnf(clause35,negated_conjecture,
    ( ~ ssSkC0
    | of(skc17,skc20,skc21) ) ).

cnf(clause36,negated_conjecture,
    ( ssSkC0
    | be(skc29,skc30,skc31,skc31) ) ).

cnf(clause37,negated_conjecture,
    ( ~ ssSkC0
    | be(skc17,skc18,skc21,skc19) ) ).

cnf(clause38,negated_conjecture,
    ( ~ man(skc33,U)
    | ssSkC0
    | event(skc33,skf9(V)) ) ).

cnf(clause39,negated_conjecture,
    ( ~ man(skc33,U)
    | ssSkC0
    | present(skc33,skf9(V)) ) ).

cnf(clause40,negated_conjecture,
    ( ~ man(skc33,U)
    | ssSkC0
    | smoke(skc33,skf9(V)) ) ).

cnf(clause41,negated_conjecture,
    ( ~ man(skc22,U)
    | ~ ssSkC0
    | event(skc22,skf5(V)) ) ).

cnf(clause42,negated_conjecture,
    ( ~ man(skc22,U)
    | ~ ssSkC0
    | present(skc22,skf5(V)) ) ).

cnf(clause43,negated_conjecture,
    ( ~ man(skc22,U)
    | ~ ssSkC0
    | smoke(skc22,skf5(V)) ) ).

cnf(clause44,negated_conjecture,
    ( ~ man(skc33,U)
    | ssSkC0
    | agent(skc33,skf9(U),U) ) ).

cnf(clause45,negated_conjecture,
    ( ~ man(skc22,U)
    | ~ ssSkC0
    | agent(skc22,skf5(U),U) ) ).

cnf(clause46,negated_conjecture,
    ( ~ proposition(U,V)
    | ~ accessible_world(U,V)
    | ~ think_believe_consider(U,W)
    | ~ present(U,W)
    | ~ event(U,W)
    | ~ theme(U,W,V)
    | ~ vincent_forename(U,X)
    | ~ forename(U,X)
    | ~ agent(U,W,Y)
    | ~ man(U,Y)
    | ~ of(U,X,Y)
    | ~ state(U,Z)
    | ~ man(U,X1)
    | ~ be(U,Z,X1,X1)
    | ~ forename(U,X2)
    | ~ jules_forename(U,X2)
    | ~ of(U,X2,X1)
    | ~ actual_world(U)
    | ~ ssSkC0
    | man(V,skf7(V)) ) ).

cnf(clause47,negated_conjecture,
    ( ~ proposition(U,V)
    | ~ accessible_world(U,V)
    | ~ think_believe_consider(U,W)
    | ~ present(U,W)
    | ~ event(U,W)
    | ~ theme(U,W,V)
    | ~ vincent_forename(U,X)
    | ~ forename(U,X)
    | ~ agent(U,W,Y)
    | ~ man(U,Y)
    | ~ of(U,X,Y)
    | ~ state(U,Z)
    | ~ man(U,X1)
    | ~ jules_forename(U,X2)
    | ~ forename(U,X2)
    | ~ be(U,Z,X3,X1)
    | ~ man(U,X3)
    | ~ of(U,X2,X3)
    | ~ actual_world(U)
    | ssSkC0
    | man(V,skf11(V)) ) ).

cnf(clause48,negated_conjecture,
    ( ~ proposition(U,V)
    | ~ accessible_world(U,V)
    | ~ smoke(V,W)
    | ~ present(V,W)
    | ~ agent(V,W,skf7(V))
    | ~ event(V,W)
    | ~ think_believe_consider(U,X)
    | ~ present(U,X)
    | ~ event(U,X)
    | ~ theme(U,X,V)
    | ~ vincent_forename(U,Y)
    | ~ forename(U,Y)
    | ~ agent(U,X,Z)
    | ~ man(U,Z)
    | ~ of(U,Y,Z)
    | ~ state(U,X1)
    | ~ man(U,X2)
    | ~ be(U,X1,X2,X2)
    | ~ forename(U,X3)
    | ~ jules_forename(U,X3)
    | ~ of(U,X3,X2)
    | ~ actual_world(U)
    | ~ ssSkC0 ) ).

cnf(clause49,negated_conjecture,
    ( ~ proposition(U,V)
    | ~ accessible_world(U,V)
    | ~ smoke(V,W)
    | ~ present(V,W)
    | ~ agent(V,W,skf11(V))
    | ~ event(V,W)
    | ~ think_believe_consider(U,X)
    | ~ present(U,X)
    | ~ event(U,X)
    | ~ theme(U,X,V)
    | ~ vincent_forename(U,Y)
    | ~ forename(U,Y)
    | ~ agent(U,X,Z)
    | ~ man(U,Z)
    | ~ of(U,Y,Z)
    | ~ state(U,X1)
    | ~ man(U,X2)
    | ~ jules_forename(U,X3)
    | ~ forename(U,X3)
    | ~ be(U,X1,X4,X2)
    | ~ man(U,X4)
    | ~ of(U,X3,X4)
    | ~ actual_world(U)
    | ssSkC0 ) ).

%--------------------------------------------------------------------------
