%--------------------------------------------------------------------------
% File     : NLP231-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Vincent believes that every man smokes, problem 12
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Vincent believes that every man smokes. Jules is a man.
%            Vincent believes that jules smokes."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0, 0.50 v2.4.0
% Syntax   : Number of clauses     :   84 (   2 unt;  40 nHn;  78 RR)
%            Number of literals    :  318 (   0 equ; 195 neg)
%            Maximal clause size   :   41 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   17 (  17 usr;   1 prp; 0-4 aty)
%            Number of functors    :   32 (  32 usr;  28 con; 0-1 aty)
%            Number of variables   :   70 (  12 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP231+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc45) ).

cnf(clause2,negated_conjecture,
    actual_world(skc28) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | accessible_world(skc45,skc55) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | proposition(skc45,skc55) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | event(skc45,skc56) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | present(skc45,skc56) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | think_believe_consider(skc45,skc56) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | forename(skc45,skc57) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | vincent_forename(skc45,skc57) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | man(skc45,skc58) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | state(skc45,skc50) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | forename(skc45,skc54) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | jules_forename(skc45,skc54) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | smoke(skc46,skc53) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkC0
    | present(skc46,skc53) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkC0
    | event(skc46,skc53) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkC0
    | man(skc45,skc51) ) ).

cnf(clause18,negated_conjecture,
    ( ssSkC0
    | jules_forename(skc45,skc52) ) ).

cnf(clause19,negated_conjecture,
    ( ssSkC0
    | forename(skc45,skc52) ) ).

cnf(clause20,negated_conjecture,
    ( ssSkC0
    | proposition(skc45,skc46) ) ).

cnf(clause21,negated_conjecture,
    ( ssSkC0
    | accessible_world(skc45,skc46) ) ).

cnf(clause22,negated_conjecture,
    ( ssSkC0
    | think_believe_consider(skc45,skc47) ) ).

cnf(clause23,negated_conjecture,
    ( ssSkC0
    | present(skc45,skc47) ) ).

cnf(clause24,negated_conjecture,
    ( ssSkC0
    | event(skc45,skc47) ) ).

cnf(clause25,negated_conjecture,
    ( ssSkC0
    | vincent_forename(skc45,skc48) ) ).

cnf(clause26,negated_conjecture,
    ( ssSkC0
    | forename(skc45,skc48) ) ).

cnf(clause27,negated_conjecture,
    ( ssSkC0
    | man(skc45,skc49) ) ).

cnf(clause28,negated_conjecture,
    ( ~ ssSkC0
    | accessible_world(skc28,skc38) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | proposition(skc28,skc38) ) ).

cnf(clause30,negated_conjecture,
    ( ~ ssSkC0
    | event(skc28,skc39) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | present(skc28,skc39) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | think_believe_consider(skc28,skc39) ) ).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc28,skc40) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | vincent_forename(skc28,skc40) ) ).

cnf(clause35,negated_conjecture,
    ( ~ ssSkC0
    | man(skc28,skc41) ) ).

cnf(clause36,negated_conjecture,
    ( ~ ssSkC0
    | state(skc28,skc35) ) ).

cnf(clause37,negated_conjecture,
    ( ~ ssSkC0
    | man(skc28,skc36) ) ).

cnf(clause38,negated_conjecture,
    ( ~ ssSkC0
    | jules_forename(skc28,skc37) ) ).

cnf(clause39,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc28,skc37) ) ).

cnf(clause40,negated_conjecture,
    ( ~ ssSkC0
    | proposition(skc28,skc29) ) ).

cnf(clause41,negated_conjecture,
    ( ~ ssSkC0
    | accessible_world(skc28,skc29) ) ).

cnf(clause42,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc28,skc31) ) ).

cnf(clause43,negated_conjecture,
    ( ~ ssSkC0
    | vincent_forename(skc28,skc31) ) ).

cnf(clause44,negated_conjecture,
    ( ~ ssSkC0
    | man(skc28,skc32) ) ).

cnf(clause45,negated_conjecture,
    ( ~ ssSkC0
    | smoke(skc29,skc34) ) ).

cnf(clause46,negated_conjecture,
    ( ~ ssSkC0
    | present(skc29,skc34) ) ).

cnf(clause47,negated_conjecture,
    ( ~ ssSkC0
    | event(skc29,skc34) ) ).

cnf(clause48,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc28,skc33) ) ).

cnf(clause49,negated_conjecture,
    ( ~ ssSkC0
    | jules_forename(skc28,skc33) ) ).

cnf(clause50,negated_conjecture,
    ( ~ ssSkC0
    | think_believe_consider(skc28,skc30) ) ).

cnf(clause51,negated_conjecture,
    ( ~ ssSkC0
    | present(skc28,skc30) ) ).

cnf(clause52,negated_conjecture,
    ( ~ ssSkC0
    | event(skc28,skc30) ) ).

cnf(clause53,negated_conjecture,
    ( ssSkC0
    | theme(skc45,skc56,skc55) ) ).

cnf(clause54,negated_conjecture,
    ( ssSkC0
    | of(skc45,skc57,skc58) ) ).

cnf(clause55,negated_conjecture,
    ( ssSkC0
    | agent(skc45,skc56,skc58) ) ).

cnf(clause56,negated_conjecture,
    ( ssSkC0
    | of(skc45,skc54,skc51) ) ).

cnf(clause57,negated_conjecture,
    ( ssSkC0
    | agent(skc46,skc53,skc51) ) ).

cnf(clause58,negated_conjecture,
    ( ssSkC0
    | of(skc45,skc52,skc51) ) ).

cnf(clause59,negated_conjecture,
    ( ssSkC0
    | theme(skc45,skc47,skc46) ) ).

cnf(clause60,negated_conjecture,
    ( ssSkC0
    | agent(skc45,skc47,skc49) ) ).

cnf(clause61,negated_conjecture,
    ( ssSkC0
    | of(skc45,skc48,skc49) ) ).

cnf(clause62,negated_conjecture,
    ( ~ ssSkC0
    | theme(skc28,skc39,skc38) ) ).

cnf(clause63,negated_conjecture,
    ( ~ ssSkC0
    | of(skc28,skc40,skc41) ) ).

cnf(clause64,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc28,skc39,skc41) ) ).

cnf(clause65,negated_conjecture,
    ( ~ ssSkC0
    | of(skc28,skc37,skc36) ) ).

cnf(clause66,negated_conjecture,
    ( ~ ssSkC0
    | of(skc28,skc31,skc32) ) ).

cnf(clause67,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc28,skc30,skc32) ) ).

cnf(clause68,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc29,skc34,skc32) ) ).

cnf(clause69,negated_conjecture,
    ( ~ ssSkC0
    | of(skc28,skc33,skc32) ) ).

cnf(clause70,negated_conjecture,
    ( ~ ssSkC0
    | theme(skc28,skc30,skc29) ) ).

cnf(clause71,negated_conjecture,
    ( ssSkC0
    | be(skc45,skc50,skc51,skc51) ) ).

cnf(clause72,negated_conjecture,
    ( ~ ssSkC0
    | be(skc28,skc35,skc36,skc36) ) ).

cnf(clause73,negated_conjecture,
    ( ~ man(skc55,U)
    | ssSkC0
    | event(skc55,skf9(V)) ) ).

cnf(clause74,negated_conjecture,
    ( ~ man(skc55,U)
    | ssSkC0
    | present(skc55,skf9(V)) ) ).

cnf(clause75,negated_conjecture,
    ( ~ man(skc55,U)
    | ssSkC0
    | smoke(skc55,skf9(V)) ) ).

cnf(clause76,negated_conjecture,
    ( ~ man(skc38,U)
    | ~ ssSkC0
    | event(skc38,skf5(V)) ) ).

cnf(clause77,negated_conjecture,
    ( ~ man(skc38,U)
    | ~ ssSkC0
    | present(skc38,skf5(V)) ) ).

cnf(clause78,negated_conjecture,
    ( ~ man(skc38,U)
    | ~ ssSkC0
    | smoke(skc38,skf5(V)) ) ).

cnf(clause79,negated_conjecture,
    ( ~ man(skc55,U)
    | ssSkC0
    | agent(skc55,skf9(U),U) ) ).

cnf(clause80,negated_conjecture,
    ( ~ man(skc38,U)
    | ~ ssSkC0
    | agent(skc38,skf5(U),U) ) ).

cnf(clause81,negated_conjecture,
    ( ~ accessible_world(U,V)
    | ~ proposition(U,V)
    | ~ theme(U,W,V)
    | ~ event(U,W)
    | ~ present(U,W)
    | ~ think_believe_consider(U,W)
    | ~ forename(U,X)
    | ~ vincent_forename(U,X)
    | ~ of(U,X,Y)
    | ~ man(U,Y)
    | ~ agent(U,W,Y)
    | ~ state(U,Z)
    | ~ smoke(X1,X2)
    | ~ present(X1,X2)
    | ~ agent(X1,X2,X3)
    | ~ event(X1,X2)
    | ~ be(U,Z,X3,X3)
    | ~ man(U,X3)
    | ~ of(U,X4,X3)
    | ~ jules_forename(U,X4)
    | ~ forename(U,X4)
    | ~ proposition(U,X1)
    | ~ accessible_world(U,X1)
    | ~ think_believe_consider(U,X5)
    | ~ present(U,X5)
    | ~ event(U,X5)
    | ~ theme(U,X5,X1)
    | ~ vincent_forename(U,X6)
    | ~ forename(U,X6)
    | ~ agent(U,X5,X7)
    | ~ man(U,X7)
    | ~ of(U,X6,X7)
    | ~ actual_world(U)
    | ~ ssSkC0
    | man(V,skf7(V)) ) ).

cnf(clause82,negated_conjecture,
    ( ~ accessible_world(U,V)
    | ~ proposition(U,V)
    | ~ theme(U,W,V)
    | ~ event(U,W)
    | ~ present(U,W)
    | ~ think_believe_consider(U,W)
    | ~ forename(U,X)
    | ~ vincent_forename(U,X)
    | ~ of(U,X,Y)
    | ~ man(U,Y)
    | ~ agent(U,W,Y)
    | ~ state(U,Z)
    | ~ be(U,Z,X1,X1)
    | ~ man(U,X1)
    | ~ of(U,X2,X1)
    | ~ jules_forename(U,X2)
    | ~ forename(U,X2)
    | ~ proposition(U,X3)
    | ~ accessible_world(U,X3)
    | ~ forename(U,X4)
    | ~ vincent_forename(U,X4)
    | ~ of(U,X4,X5)
    | ~ man(U,X5)
    | ~ agent(U,X6,X5)
    | ~ smoke(X3,X7)
    | ~ present(X3,X7)
    | ~ agent(X3,X7,X5)
    | ~ event(X3,X7)
    | ~ forename(U,X8)
    | ~ jules_forename(U,X8)
    | ~ of(U,X8,X5)
    | ~ think_believe_consider(U,X6)
    | ~ present(U,X6)
    | ~ event(U,X6)
    | ~ theme(U,X6,X3)
    | ~ actual_world(U)
    | ssSkC0
    | man(V,skf11(V)) ) ).

cnf(clause83,negated_conjecture,
    ( ~ smoke(U,V)
    | ~ present(U,V)
    | ~ agent(U,V,skf7(U))
    | ~ event(U,V)
    | ~ accessible_world(W,U)
    | ~ proposition(W,U)
    | ~ theme(W,X,U)
    | ~ event(W,X)
    | ~ present(W,X)
    | ~ think_believe_consider(W,X)
    | ~ forename(W,Y)
    | ~ vincent_forename(W,Y)
    | ~ of(W,Y,Z)
    | ~ man(W,Z)
    | ~ agent(W,X,Z)
    | ~ state(W,X1)
    | ~ smoke(X2,X3)
    | ~ present(X2,X3)
    | ~ agent(X2,X3,X4)
    | ~ event(X2,X3)
    | ~ be(W,X1,X4,X4)
    | ~ man(W,X4)
    | ~ of(W,X5,X4)
    | ~ jules_forename(W,X5)
    | ~ forename(W,X5)
    | ~ proposition(W,X2)
    | ~ accessible_world(W,X2)
    | ~ think_believe_consider(W,X6)
    | ~ present(W,X6)
    | ~ event(W,X6)
    | ~ theme(W,X6,X2)
    | ~ vincent_forename(W,X7)
    | ~ forename(W,X7)
    | ~ agent(W,X6,X8)
    | ~ man(W,X8)
    | ~ of(W,X7,X8)
    | ~ actual_world(W)
    | ~ ssSkC0 ) ).

cnf(clause84,negated_conjecture,
    ( ~ smoke(U,V)
    | ~ present(U,V)
    | ~ agent(U,V,skf11(U))
    | ~ event(U,V)
    | ~ accessible_world(W,U)
    | ~ proposition(W,U)
    | ~ theme(W,X,U)
    | ~ event(W,X)
    | ~ present(W,X)
    | ~ think_believe_consider(W,X)
    | ~ forename(W,Y)
    | ~ vincent_forename(W,Y)
    | ~ of(W,Y,Z)
    | ~ man(W,Z)
    | ~ agent(W,X,Z)
    | ~ state(W,X1)
    | ~ be(W,X1,X2,X2)
    | ~ man(W,X2)
    | ~ of(W,X3,X2)
    | ~ jules_forename(W,X3)
    | ~ forename(W,X3)
    | ~ proposition(W,X4)
    | ~ accessible_world(W,X4)
    | ~ forename(W,X5)
    | ~ vincent_forename(W,X5)
    | ~ of(W,X5,X6)
    | ~ man(W,X6)
    | ~ agent(W,X7,X6)
    | ~ smoke(X4,X8)
    | ~ present(X4,X8)
    | ~ agent(X4,X8,X6)
    | ~ event(X4,X8)
    | ~ forename(W,X9)
    | ~ jules_forename(W,X9)
    | ~ of(W,X9,X6)
    | ~ think_believe_consider(W,X7)
    | ~ present(W,X7)
    | ~ event(W,X7)
    | ~ theme(W,X7,X4)
    | ~ actual_world(W)
    | ssSkC0 ) ).

%--------------------------------------------------------------------------
