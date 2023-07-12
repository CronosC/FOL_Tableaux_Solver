%--------------------------------------------------------------------------
% File     : COM003-1 : TPTP v8.1.2. Bugfixed v1.0.1.
% Domain   : Computing Theory
% Problem  : The halting problem is undecidable
% Version  : [Bur87b] axioms.
% English  :

% Refs     : [Bur87a] Burkholder (1987), The Halting Problem
%          : [Bur87b] Burkholder (1987), A 76th Automated Theorem Proving Pr
% Source   : [Bur87b]
% Names    : - [Bur87b]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.4.0, 0.33 v7.0.0, 0.25 v6.3.0, 0.29 v6.2.0, 0.11 v6.1.0, 0.14 v6.0.0, 0.29 v5.5.0, 0.50 v5.2.0, 0.30 v5.1.0, 0.45 v5.0.0, 0.57 v4.1.0, 0.50 v4.0.1, 0.40 v4.0.0, 0.57 v3.4.0, 0.75 v3.3.0, 0.67 v3.2.0, 0.33 v3.1.0, 0.50 v2.7.0, 0.38 v2.6.0, 0.67 v2.5.0, 0.60 v2.3.0, 0.33 v2.2.1, 0.75 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   50 (   1 unt;  32 nHn;  43 RR)
%            Number of literals    :  275 (   0 equ; 185 neg)
%            Maximal clause size   :    7 (   5 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 1-3 aty)
%            Number of functors    :   12 (  12 usr;   6 con; 0-1 aty)
%            Number of variables   :   98 (   7 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
% Bugfixes : v1.0.1 - All the axiom clauses replaced. Error due
%            to incorrect use of formed in the conversion (my fault).
%--------------------------------------------------------------------------
% ((exists X (algorithm(X) &
%             (all Y (program(Y) ->
%                     (all Z decides(X,Y,Z)))))) ->
%  (exists W (program(W) &
%             (all Y (program(Y) ->
%                     (all Z decides(W,Y,Z))))))).
cnf(hypothesis_1_1,hypothesis,
    ( ~ algorithm(X)
    | program(f2(X))
    | program(c1) ) ).

cnf(hypothesis_1_2,hypothesis,
    ( ~ algorithm(X)
    | program(f2(X))
    | ~ program(Y)
    | decides(c1,Y,Z) ) ).

cnf(hypothesis_1_3,hypothesis,
    ( ~ algorithm(X)
    | ~ decides(X,f2(X),f1(X))
    | program(c1) ) ).

cnf(hypothesis_1_4,hypothesis,
    ( ~ algorithm(X)
    | ~ decides(X,f2(X),f1(X))
    | ~ program(Y)
    | decides(c1,Y,Z) ) ).

% (all W ((program(W) &
%          (all Y (program(Y) ->
%                  (all Z decides(W,Y,Z))))) ->
%         (all Y (all Z (((program(Y) &
%                          halts2(Y,Z)) ->
%                         (halts3(W,Y,Z) &
%                          outputs(W,good))) &
%                        ((program(Y) &
%                          -halts2(Y,Z)) ->
%                         (halts3(W,Y,Z) &
%                          outputs(W,bad)))))))).
cnf(hypothesis_2_1,hypothesis,
    ( ~ program(W)
    | program(f4(W))
    | ~ program(Y)
    | ~ halts2(Y,Z)
    | halts3(W,Y,Z) ) ).

cnf(hypothesis_2_2,hypothesis,
    ( ~ program(W)
    | program(f4(W))
    | ~ program(Y)
    | ~ halts2(Y,Z)
    | outputs(W,good) ) ).

cnf(hypothesis_2_3,hypothesis,
    ( ~ program(W)
    | program(f4(W))
    | ~ program(Y)
    | halts2(Y,Z)
    | halts3(W,Y,Z) ) ).

cnf(hypothesis_2_4,hypothesis,
    ( ~ program(W)
    | program(f4(W))
    | ~ program(Y)
    | halts2(Y,Z)
    | outputs(W,bad) ) ).

cnf(hypothesis_2_5,hypothesis,
    ( ~ program(W)
    | ~ decides(W,f4(W),f3(W))
    | ~ program(Y)
    | ~ halts2(Y,Z)
    | halts3(W,Y,Z) ) ).

cnf(hypothesis_2_6,hypothesis,
    ( ~ program(W)
    | ~ decides(W,f4(W),f3(W))
    | ~ program(Y)
    | ~ halts2(Y,Z)
    | outputs(W,good) ) ).

cnf(hypothesis_2_7,hypothesis,
    ( ~ program(W)
    | ~ decides(W,f4(W),f3(W))
    | ~ program(Y)
    | halts2(Y,Z)
    | halts3(W,Y,Z) ) ).

cnf(hypothesis_2_8,hypothesis,
    ( ~ program(W)
    | ~ decides(W,f4(W),f3(W))
    | ~ program(Y)
    | halts2(Y,Z)
    | outputs(W,bad) ) ).

% ((exists W (program(W) &
%             (all Y (((program(Y) &
%                       halts2(Y,Y)) ->
%                      (halts3(W,Y,Y) &
%                       outputs(W,good))) &
%                     ((program(Y) &
%                       -halts2(Y,Y)) ->
%                      (halts3(W,Y,Y) &
%                       outputs(W,bad))))))) ->
%  (exists V (program(V) &
%             (all Y (((program(Y) &
%                       halts2(Y,Y)) ->
%                      (halts2(V,Y) &
%                       outputs(V,good))) &
%                     ((program(Y) &
%                       -halts2(Y,Y)) ->
%                      (halts2(V,Y) &
%                       outputs(V,bad)))))))).
cnf(hypothesis_3_1,hypothesis,
    ( ~ program(W)
    | program(f5(W))
    | program(c2) ) ).

cnf(hypothesis_3_2,hypothesis,
    ( ~ program(W)
    | program(f5(W))
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | halts2(c2,Y) ) ).

cnf(hypothesis_3_3,hypothesis,
    ( ~ program(W)
    | program(f5(W))
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | outputs(c2,good) ) ).

cnf(hypothesis_3_4,hypothesis,
    ( ~ program(W)
    | program(f5(W))
    | ~ program(Y)
    | halts2(Y,Y)
    | halts2(c2,Y) ) ).

cnf(hypothesis_3_5,hypothesis,
    ( ~ program(W)
    | program(f5(W))
    | ~ program(Y)
    | halts2(Y,Y)
    | outputs(c2,bad) ) ).

cnf(hypothesis_3_6,hypothesis,
    ( ~ program(W)
    | halts2(f5(W),f5(W))
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,bad)
    | program(c2) ) ).

cnf(hypothesis_3_7,hypothesis,
    ( ~ program(W)
    | halts2(f5(W),f5(W))
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,bad)
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | halts2(c2,Y) ) ).

cnf(hypothesis_3_8,hypothesis,
    ( ~ program(W)
    | halts2(f5(W),f5(W))
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,bad)
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | outputs(c2,good) ) ).

cnf(hypothesis_3_9,hypothesis,
    ( ~ program(W)
    | halts2(f5(W),f5(W))
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,bad)
    | ~ program(Y)
    | halts2(Y,Y)
    | halts2(c2,Y) ) ).

cnf(hypothesis_3_10,hypothesis,
    ( ~ program(W)
    | halts2(f5(W),f5(W))
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,bad)
    | ~ program(Y)
    | halts2(Y,Y)
    | outputs(c2,bad) ) ).

cnf(hypothesis_3_11,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ halts2(f5(W),f5(W))
    | program(c2) ) ).

cnf(hypothesis_3_12,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ halts2(f5(W),f5(W))
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | halts2(c2,Y) ) ).

cnf(hypothesis_3_13,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ halts2(f5(W),f5(W))
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | outputs(c2,good) ) ).

cnf(hypothesis_3_14,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ halts2(f5(W),f5(W))
    | ~ program(Y)
    | halts2(Y,Y)
    | halts2(c2,Y) ) ).

cnf(hypothesis_3_15,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ halts2(f5(W),f5(W))
    | ~ program(Y)
    | halts2(Y,Y)
    | outputs(c2,bad) ) ).

cnf(hypothesis_3_16,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ outputs(W,bad)
    | program(c2) ) ).

cnf(hypothesis_3_17,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ outputs(W,bad)
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | halts2(c2,Y) ) ).

cnf(hypothesis_3_18,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ outputs(W,bad)
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | outputs(c2,good) ) ).

cnf(hypothesis_3_19,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ outputs(W,bad)
    | ~ program(Y)
    | halts2(Y,Y)
    | halts2(c2,Y) ) ).

cnf(hypothesis_3_20,hypothesis,
    ( ~ program(W)
    | ~ halts3(W,f5(W),f5(W))
    | ~ outputs(W,good)
    | ~ outputs(W,bad)
    | ~ program(Y)
    | halts2(Y,Y)
    | outputs(c2,bad) ) ).

% ((exists V (program(V) &
%             (all Y (((program(Y) &
%                       halts2(Y,Y)) ->
%                      (halts2(V,Y) &
%                       outputs(V,good))) &
%                     ((program(Y) &
%                       -halts2(Y,Y)) ->
%                      (halts2(V,Y) &
%                       outputs(V,bad))))))) ->
%  (exists U (program(U) &
%             (all Y (((program(Y) &
%                        halts2(Y,Y)) ->
%                      -halts2(U,Y)) &
%                     ((program(Y) &
%                       -halts2(Y,Y)) ->
%                      (halts2(U,Y) &
%                       outputs(U,bad)))))))).
cnf(hypothesis_4_1,hypothesis,
    ( ~ program(V)
    | program(f6(V))
    | program(c3) ) ).

cnf(hypothesis_4_2,hypothesis,
    ( ~ program(V)
    | program(f6(V))
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | ~ halts2(c3,Y) ) ).

cnf(hypothesis_4_3,hypothesis,
    ( ~ program(V)
    | program(f6(V))
    | ~ program(Y)
    | halts2(Y,Y)
    | halts2(c3,Y) ) ).

cnf(hypothesis_4_4,hypothesis,
    ( ~ program(V)
    | program(f6(V))
    | ~ program(Y)
    | halts2(Y,Y)
    | outputs(c3,bad) ) ).

cnf(hypothesis_4_5,hypothesis,
    ( ~ program(V)
    | halts2(f6(V),f6(V))
    | ~ halts2(V,f6(V))
    | ~ outputs(V,bad)
    | program(c3) ) ).

cnf(hypothesis_4_6,hypothesis,
    ( ~ program(V)
    | halts2(f6(V),f6(V))
    | ~ halts2(V,f6(V))
    | ~ outputs(V,bad)
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | ~ halts2(c3,Y) ) ).

cnf(hypothesis_4_7,hypothesis,
    ( ~ program(V)
    | halts2(f6(V),f6(V))
    | ~ halts2(V,f6(V))
    | ~ outputs(V,bad)
    | ~ program(Y)
    | halts2(Y,Y)
    | halts2(c3,Y) ) ).

cnf(hypothesis_4_8,hypothesis,
    ( ~ program(V)
    | halts2(f6(V),f6(V))
    | ~ halts2(V,f6(V))
    | ~ outputs(V,bad)
    | ~ program(Y)
    | halts2(Y,Y)
    | outputs(c3,bad) ) ).

cnf(hypothesis_4_9,hypothesis,
    ( ~ program(V)
    | ~ halts2(V,f6(V))
    | ~ outputs(V,good)
    | ~ halts2(f6(V),f6(V))
    | program(c3) ) ).

cnf(hypothesis_4_10,hypothesis,
    ( ~ program(V)
    | ~ halts2(V,f6(V))
    | ~ outputs(V,good)
    | ~ halts2(f6(V),f6(V))
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | ~ halts2(c3,Y) ) ).

cnf(hypothesis_4_11,hypothesis,
    ( ~ program(V)
    | ~ halts2(V,f6(V))
    | ~ outputs(V,good)
    | ~ halts2(f6(V),f6(V))
    | ~ program(Y)
    | halts2(Y,Y)
    | halts2(c3,Y) ) ).

cnf(hypothesis_4_12,hypothesis,
    ( ~ program(V)
    | ~ halts2(V,f6(V))
    | ~ outputs(V,good)
    | ~ halts2(f6(V),f6(V))
    | ~ program(Y)
    | halts2(Y,Y)
    | outputs(c3,bad) ) ).

cnf(hypothesis_4_13,hypothesis,
    ( ~ program(V)
    | ~ halts2(V,f6(V))
    | ~ outputs(V,good)
    | ~ outputs(V,bad)
    | program(c3) ) ).

cnf(hypothesis_4_14,hypothesis,
    ( ~ program(V)
    | ~ halts2(V,f6(V))
    | ~ outputs(V,good)
    | ~ outputs(V,bad)
    | ~ program(Y)
    | ~ halts2(Y,Y)
    | ~ halts2(c3,Y) ) ).

cnf(hypothesis_4_15,hypothesis,
    ( ~ program(V)
    | ~ halts2(V,f6(V))
    | ~ outputs(V,good)
    | ~ outputs(V,bad)
    | ~ program(Y)
    | halts2(Y,Y)
    | halts2(c3,Y) ) ).

cnf(hypothesis_4_17,hypothesis,
    ( ~ program(V)
    | ~ halts2(V,f6(V))
    | ~ outputs(V,good)
    | ~ outputs(V,bad)
    | ~ program(Y)
    | halts2(Y,Y)
    | outputs(c3,bad) ) ).

%----Prove this is impossible
% (exists X1 (algorithm(X1) &
%             (all Y1 (program(Y1) ->
%                      (all Z1 decides(X1,Y1,Z1)))))).
cnf(a_deciding_algorithm,negated_conjecture,
    algorithm(c4) ).

cnf(prove_the_algorithm_doesnt_exist,negated_conjecture,
    ( ~ program(Y1)
    | decides(c4,Y1,Z1) ) ).

%--------------------------------------------------------------------------
