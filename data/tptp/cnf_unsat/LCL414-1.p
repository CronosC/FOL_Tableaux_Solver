%--------------------------------------------------------------------------
% File     : LCL414-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Syntactic
% Problem  : Peter Andrews Problem THM147
% Version  : Especial.
% English  :

% Refs     : [And97] Andrews (1994), Email to G. Sutcliffe
% Source   : [And97]
% Names    : THM147 [And97]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.5.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    3 (   3 usr;   1 con; 0-2 aty)
%            Number of variables   :    9 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(thm147_1,negated_conjecture,
    ( a_truth(B)
    | ~ a_truth(A)
    | ~ a_truth(implies(A,B)) ) ).

cnf(thm147_2,negated_conjecture,
    a_truth(implies(A,implies(B,A))) ).

cnf(thm147_3,negated_conjecture,
    a_truth(implies(implies(A,implies(B,C)),implies(implies(A,B),implies(A,C)))) ).

cnf(thm147_4,negated_conjecture,
    a_truth(implies(implies(not(A),not(B)),implies(B,A))) ).

cnf(thm147_5,negated_conjecture,
    ~ a_truth(implies(sk1,sk1)) ).

%--------------------------------------------------------------------------
