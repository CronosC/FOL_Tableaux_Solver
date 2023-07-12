%--------------------------------------------------------------------------
% File     : NLP223-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Vincent believes that every man smokes, problem 4
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Vincent believes that every man smokes. Jules is a man."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0, 0.17 v2.4.0
% Syntax   : Number of clauses     :   48 (   2 unt;  22 nHn;  42 RR)
%            Number of literals    :  180 (   0 equ; 111 neg)
%            Maximal clause size   :   23 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   17 (  17 usr;   1 prp; 0-4 aty)
%            Number of functors    :   20 (  20 usr;  16 con; 0-1 aty)
%            Number of variables   :   48 (  12 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP223+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc27) ).

cnf(clause2,negated_conjecture,
    actual_world(skc16) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | proposition(skc27,skc31) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | accessible_world(skc27,skc31) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | think_believe_consider(skc27,skc32) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | present(skc27,skc32) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | event(skc27,skc32) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | vincent_forename(skc27,skc33) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | forename(skc27,skc33) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | man(skc27,skc34) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | state(skc27,skc28) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | man(skc27,skc29) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | forename(skc27,skc30) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | jules_forename(skc27,skc30) ) ).

cnf(clause15,negated_conjecture,
    ( ~ ssSkC0
    | state(skc16,skc17) ) ).

cnf(clause16,negated_conjecture,
    ( ~ ssSkC0
    | man(skc16,skc18) ) ).

cnf(clause17,negated_conjecture,
    ( ~ ssSkC0
    | accessible_world(skc16,skc19) ) ).

cnf(clause18,negated_conjecture,
    ( ~ ssSkC0
    | proposition(skc16,skc19) ) ).

cnf(clause19,negated_conjecture,
    ( ~ ssSkC0
    | event(skc16,skc20) ) ).

cnf(clause20,negated_conjecture,
    ( ~ ssSkC0
    | present(skc16,skc20) ) ).

cnf(clause21,negated_conjecture,
    ( ~ ssSkC0
    | think_believe_consider(skc16,skc20) ) ).

cnf(clause22,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc16,skc21) ) ).

cnf(clause23,negated_conjecture,
    ( ~ ssSkC0
    | vincent_forename(skc16,skc21) ) ).

cnf(clause24,negated_conjecture,
    ( ~ ssSkC0
    | man(skc16,skc22) ) ).

cnf(clause25,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc16,skc23) ) ).

cnf(clause26,negated_conjecture,
    ( ~ ssSkC0
    | jules_forename(skc16,skc23) ) ).

cnf(clause27,negated_conjecture,
    ( ssSkC0
    | theme(skc27,skc32,skc31) ) ).

cnf(clause28,negated_conjecture,
    ( ssSkC0
    | agent(skc27,skc32,skc34) ) ).

cnf(clause29,negated_conjecture,
    ( ssSkC0
    | of(skc27,skc33,skc34) ) ).

cnf(clause30,negated_conjecture,
    ( ssSkC0
    | of(skc27,skc30,skc29) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | theme(skc16,skc20,skc19) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | of(skc16,skc21,skc22) ) ).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc16,skc20,skc22) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | of(skc16,skc23,skc22) ) ).

cnf(clause35,negated_conjecture,
    ( ssSkC0
    | be(skc27,skc28,skc29,skc29) ) ).

cnf(clause36,negated_conjecture,
    ( ~ ssSkC0
    | be(skc16,skc17,skc22,skc18) ) ).

cnf(clause37,negated_conjecture,
    ( ~ man(skc31,U)
    | ssSkC0
    | event(skc31,skf11(V)) ) ).

cnf(clause38,negated_conjecture,
    ( ~ man(skc31,U)
    | ssSkC0
    | present(skc31,skf11(V)) ) ).

cnf(clause39,negated_conjecture,
    ( ~ man(skc31,U)
    | ssSkC0
    | smoke(skc31,skf11(V)) ) ).

cnf(clause40,negated_conjecture,
    ( ~ man(skc19,U)
    | ~ ssSkC0
    | event(skc19,skf7(V)) ) ).

cnf(clause41,negated_conjecture,
    ( ~ man(skc19,U)
    | ~ ssSkC0
    | present(skc19,skf7(V)) ) ).

cnf(clause42,negated_conjecture,
    ( ~ man(skc19,U)
    | ~ ssSkC0
    | smoke(skc19,skf7(V)) ) ).

cnf(clause43,negated_conjecture,
    ( ~ man(skc31,U)
    | ssSkC0
    | agent(skc31,skf11(U),U) ) ).

cnf(clause44,negated_conjecture,
    ( ~ man(skc19,U)
    | ~ ssSkC0
    | agent(skc19,skf7(U),U) ) ).

cnf(clause45,negated_conjecture,
    ( ~ state(U,V)
    | ~ man(U,W)
    | ~ accessible_world(U,X)
    | ~ proposition(U,X)
    | ~ theme(U,Y,X)
    | ~ event(U,Y)
    | ~ present(U,Y)
    | ~ think_believe_consider(U,Y)
    | ~ forename(U,Z)
    | ~ vincent_forename(U,Z)
    | ~ of(U,Z,X1)
    | ~ man(U,X1)
    | ~ agent(U,Y,X1)
    | ~ be(U,V,X1,W)
    | ~ forename(U,X2)
    | ~ jules_forename(U,X2)
    | ~ of(U,X2,X1)
    | ~ actual_world(U)
    | ssSkC0
    | man(X,skf13(X)) ) ).

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
    | man(V,skf9(V)) ) ).

cnf(clause47,negated_conjecture,
    ( ~ state(U,V)
    | ~ man(U,W)
    | ~ smoke(X,Y)
    | ~ present(X,Y)
    | ~ agent(X,Y,skf13(X))
    | ~ event(X,Y)
    | ~ accessible_world(U,X)
    | ~ proposition(U,X)
    | ~ theme(U,Z,X)
    | ~ event(U,Z)
    | ~ present(U,Z)
    | ~ think_believe_consider(U,Z)
    | ~ forename(U,X1)
    | ~ vincent_forename(U,X1)
    | ~ of(U,X1,X2)
    | ~ man(U,X2)
    | ~ agent(U,Z,X2)
    | ~ be(U,V,X2,W)
    | ~ forename(U,X3)
    | ~ jules_forename(U,X3)
    | ~ of(U,X3,X2)
    | ~ actual_world(U)
    | ssSkC0 ) ).

cnf(clause48,negated_conjecture,
    ( ~ proposition(U,V)
    | ~ accessible_world(U,V)
    | ~ smoke(V,W)
    | ~ present(V,W)
    | ~ agent(V,W,skf9(V))
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

%--------------------------------------------------------------------------
