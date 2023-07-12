%--------------------------------------------------------------------------
% File     : MSC005-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Miscellaneous
% Problem  : The evaluation of XOR expressions
% Version  : [Pla82] axioms.
% English  :

% Refs     : [Pla82] Plaisted (1982), A Simplified Problem Reduction Format
% Source   : [Pla82]
% Names    : Problem 5.1 [Pla82]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.4.0, 0.17 v7.3.0, 0.00 v5.4.0, 0.06 v5.3.0, 0.05 v5.2.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    7 (   3 unt;   0 nHn;   7 RR)
%            Number of literals    :   15 (   0 equ;   9 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    5 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    3 (   3 usr;   2 con; 0-2 aty)
%            Number of variables   :    9 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(true_is_true,axiom,
    value(truth,truth) ).

cnf(false_is_false,axiom,
    value(falsity,falsity) ).

cnf(true_xor_true,axiom,
    ( ~ value(X,truth)
    | ~ value(Y,truth)
    | value(xor(X,Y),falsity) ) ).

cnf(true_xor_false,axiom,
    ( ~ value(X,truth)
    | ~ value(Y,falsity)
    | value(xor(X,Y),truth) ) ).

cnf(false_xor_true,axiom,
    ( ~ value(X,falsity)
    | ~ value(Y,truth)
    | value(xor(X,Y),truth) ) ).

cnf(false_xor_false,axiom,
    ( ~ value(X,falsity)
    | ~ value(Y,falsity)
    | value(xor(X,Y),falsity) ) ).

cnf(evaluate_expression,negated_conjecture,
    ~ value(xor(xor(xor(xor(truth,falsity),falsity),truth),falsity),Value) ).

%--------------------------------------------------------------------------
