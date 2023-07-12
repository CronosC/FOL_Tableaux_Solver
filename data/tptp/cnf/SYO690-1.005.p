%------------------------------------------------------------------------------
% File     : SYO690-1.005 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : Loop 5 No
% Version  : Especial.
% English  :

% Refs     : [Wal17] Waldman (2017), Email to Geoff Sutcliffe
% Source   : [TPTP]
% Names    : loop-5-no.tptp [Wal17]

% Status   : Satisfiable
% Rating   : 0.33 v8.1.0, 0.00 v7.5.0, 0.33 v7.4.0, 0.67 v7.3.0
% Syntax   : Number of clauses     :   13 (   6 unt;   0 nHn;   8 RR)
%            Number of literals    :   22 (   0 equ;  11 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :   65 (  14 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 2-3 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :   33 (   8 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%------------------------------------------------------------------------------
cnf(rule_1,axiom,
    top(f(f(f(f(f(f(f(Z,a),a),a),a),a),Y),f(X,a)),f(f(X,f(f(f(f(f(f(Y,a),a),a),a),a),a)),Z)) ).

cnf(prove,negated_conjecture,
    seq(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(succ(zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),X,X) ).

cnf(rewrite_top,axiom,
    ( ~ top(X,Y)
    | step(X,Y) ) ).

cnf(rewrite_left,axiom,
    ( ~ step(X,Y)
    | step(f(X,Z),f(Y,Z)) ) ).

cnf(rewrite_right,axiom,
    ( ~ step(Y,Z)
    | step(f(X,Y),f(X,Z)) ) ).

cnf(rewrite_sequence_zero,axiom,
    seq(zero,X,X) ).

cnf(rewrite_sequence_succ,axiom,
    ( ~ seq(N,X,Y)
    | ~ step(Y,Z)
    | seq(succ(N),X,Z) ) ).

cnf(constructor_a,axiom,
    eq(a,a) ).

cnf(constructor_f1,axiom,
    ( ~ eq(P,R)
    | ~ eq(Q,S)
    | eq(f(P,Q),f(R,S)) ) ).

cnf(constructor_f2,axiom,
    ( eq(P,R)
    | ~ eq(f(P,Q),f(R,S)) ) ).

cnf(constructor_f3,axiom,
    ( eq(Q,S)
    | ~ eq(f(P,Q),f(R,S)) ) ).

cnf(constructor_af,axiom,
    ~ eq(f(X,Y),a) ).

cnf(constructor_af_001,axiom,
    ~ eq(a,f(X,Y)) ).

%------------------------------------------------------------------------------
