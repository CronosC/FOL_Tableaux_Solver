%--------------------------------------------------------------------------
% File     : SET786-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Set theory
% Problem  : Peter Andrews Problem THM25
% Version  : Especial.
% English  :

% Refs     : [And97] Andrews (1994), Email to G. Sutcliffe
% Source   : [And97]
% Names    : THM25 [And97]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.3.0, 0.14 v6.2.0, 0.00 v2.5.0
% Syntax   : Number of clauses     :    3 (   0 unt;   2 nHn;   1 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    2 (   2 usr;   1 con; 0-1 aty)
%            Number of variables   :    4 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(thm25_1,negated_conjecture,
    ( ~ element(B,A)
    | ~ element(A,B)
    | ~ element(A,sk1) ) ).

cnf(thm25_2,negated_conjecture,
    ( element(A,sk1)
    | element(A,sk2(A)) ) ).

cnf(thm25_3,negated_conjecture,
    ( element(A,sk1)
    | element(sk2(A),A) ) ).

%--------------------------------------------------------------------------
