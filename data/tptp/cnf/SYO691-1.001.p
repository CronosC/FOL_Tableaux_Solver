%------------------------------------------------------------------------------
% File     : SYO691-1.001 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : Loop 1 Yes
% Version  : Especial.
% English  :

% Refs     : [Wal17] Waldman (2017), Email to Geoff Sutcliffe
% Source   : [TPTP]
% Names    : loop-1-yes.tptp [Wal17]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.3.0
% Syntax   : Number of clauses     :    7 (   3 unt;   0 nHn;   3 RR)
%            Number of literals    :   12 (   0 equ;   6 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-3 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :   17 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%------------------------------------------------------------------------------
cnf(rule_1,axiom,
    top(f(f(f(Z,a),Y),f(X,a)),f(f(X,f(f(Y,a),a)),Z)) ).

cnf(prove,negated_conjecture,
    ~ seq(succ(succ(succ(succ(succ(zero))))),X,X) ).

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

%------------------------------------------------------------------------------
