%--------------------------------------------------------------------------
% File     : NLP232-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Natural Language Processing
% Problem  : Vincent believes that every man smokes, problem 13
% Version  : [Bos00b] axioms.
% English  : Eliminating logically equivalent interpretations in the statement
%            "Vincent believes that every man smokes. Jules is a man.
%            Vincent believes that jules smokes."

% Refs     : [Bos00a] Bos (2000), DORIS: Discourse Oriented Representation a
%            [Bos00b] Bos (2000), Applied Theorem Proving - Natural Language
% Source   : [TPTP]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v6.3.0, 0.33 v6.2.0, 0.20 v6.1.0, 0.00 v5.0.0, 0.12 v4.1.0, 0.14 v4.0.0, 0.12 v3.5.0, 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0, 0.50 v2.4.0
% Syntax   : Number of clauses     :   85 (   2 unt;  40 nHn;  79 RR)
%            Number of literals    :  322 (   0 equ; 198 neg)
%            Maximal clause size   :   42 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :   17 (  17 usr;   1 prp; 0-4 aty)
%            Number of functors    :   33 (  33 usr;  29 con; 0-1 aty)
%            Number of variables   :   72 (  12 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : Created from NLP232+1.p using FLOTTER
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    actual_world(skc47) ).

cnf(clause2,negated_conjecture,
    actual_world(skc29) ).

cnf(clause3,negated_conjecture,
    ( ssSkC0
    | accessible_world(skc47,skc57) ) ).

cnf(clause4,negated_conjecture,
    ( ssSkC0
    | proposition(skc47,skc57) ) ).

cnf(clause5,negated_conjecture,
    ( ssSkC0
    | event(skc47,skc58) ) ).

cnf(clause6,negated_conjecture,
    ( ssSkC0
    | present(skc47,skc58) ) ).

cnf(clause7,negated_conjecture,
    ( ssSkC0
    | think_believe_consider(skc47,skc58) ) ).

cnf(clause8,negated_conjecture,
    ( ssSkC0
    | forename(skc47,skc59) ) ).

cnf(clause9,negated_conjecture,
    ( ssSkC0
    | vincent_forename(skc47,skc59) ) ).

cnf(clause10,negated_conjecture,
    ( ssSkC0
    | man(skc47,skc60) ) ).

cnf(clause11,negated_conjecture,
    ( ssSkC0
    | state(skc47,skc52) ) ).

cnf(clause12,negated_conjecture,
    ( ssSkC0
    | forename(skc47,skc56) ) ).

cnf(clause13,negated_conjecture,
    ( ssSkC0
    | jules_forename(skc47,skc56) ) ).

cnf(clause14,negated_conjecture,
    ( ssSkC0
    | smoke(skc48,skc55) ) ).

cnf(clause15,negated_conjecture,
    ( ssSkC0
    | present(skc48,skc55) ) ).

cnf(clause16,negated_conjecture,
    ( ssSkC0
    | event(skc48,skc55) ) ).

cnf(clause17,negated_conjecture,
    ( ssSkC0
    | man(skc47,skc53) ) ).

cnf(clause18,negated_conjecture,
    ( ssSkC0
    | jules_forename(skc47,skc54) ) ).

cnf(clause19,negated_conjecture,
    ( ssSkC0
    | forename(skc47,skc54) ) ).

cnf(clause20,negated_conjecture,
    ( ssSkC0
    | proposition(skc47,skc48) ) ).

cnf(clause21,negated_conjecture,
    ( ssSkC0
    | accessible_world(skc47,skc48) ) ).

cnf(clause22,negated_conjecture,
    ( ssSkC0
    | think_believe_consider(skc47,skc49) ) ).

cnf(clause23,negated_conjecture,
    ( ssSkC0
    | present(skc47,skc49) ) ).

cnf(clause24,negated_conjecture,
    ( ssSkC0
    | event(skc47,skc49) ) ).

cnf(clause25,negated_conjecture,
    ( ssSkC0
    | vincent_forename(skc47,skc50) ) ).

cnf(clause26,negated_conjecture,
    ( ssSkC0
    | forename(skc47,skc50) ) ).

cnf(clause27,negated_conjecture,
    ( ssSkC0
    | man(skc47,skc51) ) ).

cnf(clause28,negated_conjecture,
    ( ~ ssSkC0
    | proposition(skc29,skc40) ) ).

cnf(clause29,negated_conjecture,
    ( ~ ssSkC0
    | accessible_world(skc29,skc40) ) ).

cnf(clause30,negated_conjecture,
    ( ~ ssSkC0
    | think_believe_consider(skc29,skc41) ) ).

cnf(clause31,negated_conjecture,
    ( ~ ssSkC0
    | present(skc29,skc41) ) ).

cnf(clause32,negated_conjecture,
    ( ~ ssSkC0
    | event(skc29,skc41) ) ).

cnf(clause33,negated_conjecture,
    ( ~ ssSkC0
    | vincent_forename(skc29,skc42) ) ).

cnf(clause34,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc29,skc42) ) ).

cnf(clause35,negated_conjecture,
    ( ~ ssSkC0
    | man(skc29,skc43) ) ).

cnf(clause36,negated_conjecture,
    ( ~ ssSkC0
    | state(skc29,skc37) ) ).

cnf(clause37,negated_conjecture,
    ( ~ ssSkC0
    | man(skc29,skc38) ) ).

cnf(clause38,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc29,skc39) ) ).

cnf(clause39,negated_conjecture,
    ( ~ ssSkC0
    | jules_forename(skc29,skc39) ) ).

cnf(clause40,negated_conjecture,
    ( ~ ssSkC0
    | accessible_world(skc29,skc30) ) ).

cnf(clause41,negated_conjecture,
    ( ~ ssSkC0
    | proposition(skc29,skc30) ) ).

cnf(clause42,negated_conjecture,
    ( ~ ssSkC0
    | jules_forename(skc29,skc34) ) ).

cnf(clause43,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc29,skc34) ) ).

cnf(clause44,negated_conjecture,
    ( ~ ssSkC0
    | smoke(skc30,skc36) ) ).

cnf(clause45,negated_conjecture,
    ( ~ ssSkC0
    | present(skc30,skc36) ) ).

cnf(clause46,negated_conjecture,
    ( ~ ssSkC0
    | event(skc30,skc36) ) ).

cnf(clause47,negated_conjecture,
    ( ~ ssSkC0
    | man(skc29,skc35) ) ).

cnf(clause48,negated_conjecture,
    ( ~ ssSkC0
    | vincent_forename(skc29,skc32) ) ).

cnf(clause49,negated_conjecture,
    ( ~ ssSkC0
    | forename(skc29,skc32) ) ).

cnf(clause50,negated_conjecture,
    ( ~ ssSkC0
    | man(skc29,skc33) ) ).

cnf(clause51,negated_conjecture,
    ( ~ ssSkC0
    | event(skc29,skc31) ) ).

cnf(clause52,negated_conjecture,
    ( ~ ssSkC0
    | present(skc29,skc31) ) ).

cnf(clause53,negated_conjecture,
    ( ~ ssSkC0
    | think_believe_consider(skc29,skc31) ) ).

cnf(clause54,negated_conjecture,
    ( ssSkC0
    | theme(skc47,skc58,skc57) ) ).

cnf(clause55,negated_conjecture,
    ( ssSkC0
    | of(skc47,skc59,skc60) ) ).

cnf(clause56,negated_conjecture,
    ( ssSkC0
    | agent(skc47,skc58,skc60) ) ).

cnf(clause57,negated_conjecture,
    ( ssSkC0
    | of(skc47,skc56,skc53) ) ).

cnf(clause58,negated_conjecture,
    ( ssSkC0
    | agent(skc48,skc55,skc53) ) ).

cnf(clause59,negated_conjecture,
    ( ssSkC0
    | of(skc47,skc54,skc53) ) ).

cnf(clause60,negated_conjecture,
    ( ssSkC0
    | theme(skc47,skc49,skc48) ) ).

cnf(clause61,negated_conjecture,
    ( ssSkC0
    | agent(skc47,skc49,skc51) ) ).

cnf(clause62,negated_conjecture,
    ( ssSkC0
    | of(skc47,skc50,skc51) ) ).

cnf(clause63,negated_conjecture,
    ( ~ ssSkC0
    | theme(skc29,skc41,skc40) ) ).

cnf(clause64,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc29,skc41,skc43) ) ).

cnf(clause65,negated_conjecture,
    ( ~ ssSkC0
    | of(skc29,skc42,skc43) ) ).

cnf(clause66,negated_conjecture,
    ( ~ ssSkC0
    | of(skc29,skc39,skc38) ) ).

cnf(clause67,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc30,skc36,skc35) ) ).

cnf(clause68,negated_conjecture,
    ( ~ ssSkC0
    | of(skc29,skc34,skc35) ) ).

cnf(clause69,negated_conjecture,
    ( ~ ssSkC0
    | agent(skc29,skc31,skc33) ) ).

cnf(clause70,negated_conjecture,
    ( ~ ssSkC0
    | of(skc29,skc32,skc33) ) ).

cnf(clause71,negated_conjecture,
    ( ~ ssSkC0
    | theme(skc29,skc31,skc30) ) ).

cnf(clause72,negated_conjecture,
    ( ssSkC0
    | be(skc47,skc52,skc53,skc53) ) ).

cnf(clause73,negated_conjecture,
    ( ~ ssSkC0
    | be(skc29,skc37,skc38,skc38) ) ).

cnf(clause74,negated_conjecture,
    ( ~ man(skc57,U)
    | ssSkC0
    | event(skc57,skf9(V)) ) ).

cnf(clause75,negated_conjecture,
    ( ~ man(skc57,U)
    | ssSkC0
    | present(skc57,skf9(V)) ) ).

cnf(clause76,negated_conjecture,
    ( ~ man(skc57,U)
    | ssSkC0
    | smoke(skc57,skf9(V)) ) ).

cnf(clause77,negated_conjecture,
    ( ~ man(skc40,U)
    | ~ ssSkC0
    | event(skc40,skf5(V)) ) ).

cnf(clause78,negated_conjecture,
    ( ~ man(skc40,U)
    | ~ ssSkC0
    | present(skc40,skf5(V)) ) ).

cnf(clause79,negated_conjecture,
    ( ~ man(skc40,U)
    | ~ ssSkC0
    | smoke(skc40,skf5(V)) ) ).

cnf(clause80,negated_conjecture,
    ( ~ man(skc57,U)
    | ssSkC0
    | agent(skc57,skf9(U),U) ) ).

cnf(clause81,negated_conjecture,
    ( ~ man(skc40,U)
    | ~ ssSkC0
    | agent(skc40,skf5(U),U) ) ).

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
    | ~ accessible_world(U,X3)
    | ~ proposition(U,X3)
    | ~ jules_forename(U,X4)
    | ~ forename(U,X4)
    | ~ smoke(X3,X5)
    | ~ present(X3,X5)
    | ~ agent(X3,X5,X6)
    | ~ event(X3,X5)
    | ~ man(U,X6)
    | ~ of(U,X4,X6)
    | ~ vincent_forename(U,X7)
    | ~ forename(U,X7)
    | ~ agent(U,X8,X9)
    | ~ man(U,X9)
    | ~ of(U,X7,X9)
    | ~ theme(U,X8,X3)
    | ~ event(U,X8)
    | ~ present(U,X8)
    | ~ think_believe_consider(U,X8)
    | ~ actual_world(U)
    | ssSkC0
    | man(V,skf11(V)) ) ).

cnf(clause85,negated_conjecture,
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
    | ~ be(U,X1,X2,X2)
    | ~ forename(U,X3)
    | ~ jules_forename(U,X3)
    | ~ of(U,X3,X2)
    | ~ accessible_world(U,X4)
    | ~ proposition(U,X4)
    | ~ jules_forename(U,X5)
    | ~ forename(U,X5)
    | ~ smoke(X4,X6)
    | ~ present(X4,X6)
    | ~ agent(X4,X6,X7)
    | ~ event(X4,X6)
    | ~ man(U,X7)
    | ~ of(U,X5,X7)
    | ~ vincent_forename(U,X8)
    | ~ forename(U,X8)
    | ~ agent(U,X9,X10)
    | ~ man(U,X10)
    | ~ of(U,X8,X10)
    | ~ theme(U,X9,X4)
    | ~ event(U,X9)
    | ~ present(U,X9)
    | ~ think_believe_consider(U,X9)
    | ~ actual_world(U)
    | ssSkC0 ) ).

%--------------------------------------------------------------------------
