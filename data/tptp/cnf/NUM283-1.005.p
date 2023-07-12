%--------------------------------------------------------------------------
% File     : NUM283-1.005 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Number Theory
% Problem  : Calculation of factorial
% Version  : [SETHEO] axioms : Biased.
% English  : Compute 5 factorial.

% Refs     :
% Source   : [SETHEO]
% Names    : fac2.lop (Size 2) [SETHEO]
%          : fac3.lop (Size 3) [SETHEO]
%          : fac4.lop (Size 4) [SETHEO]
%          : fac5.lop (Size 5) [SETHEO]
%          : fac6.lop (Size 7) [SETHEO]
%          : fac7.lop (Size 7) [SETHEO]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.1.0, 0.07 v6.0.0, 0.11 v5.5.0, 0.06 v5.4.0, 0.11 v5.3.0, 0.20 v5.2.0, 0.15 v5.1.0, 0.12 v5.0.0, 0.13 v4.0.1, 0.14 v3.4.0, 0.00 v3.1.0, 0.17 v2.7.0, 0.25 v2.6.0, 0.14 v2.5.0, 0.00 v2.4.0, 0.14 v2.3.0, 0.14 v2.2.1, 0.33 v2.2.0, 0.22 v2.1.0
% Syntax   : Number of clauses     :    7 (   4 unt;   0 nHn;   5 RR)
%            Number of literals    :   12 (   0 equ;   6 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-3 aty)
%            Number of functors    :    2 (   2 usr;   1 con; 0-1 aty)
%            Number of variables   :   13 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Biased towards SETHEO.
%          : tptp2X: -f tptp -s5 NUM283-1.g
%--------------------------------------------------------------------------
cnf(add_0,axiom,
    sum(X,n0,X) ).

cnf(add,axiom,
    ( ~ sum(X,Y,Z)
    | sum(X,s(Y),s(Z)) ) ).

cnf(times1,axiom,
    product(s(n0),X,X) ).

cnf(times,axiom,
    ( ~ sum(R,Y,Z)
    | ~ product(X,Y,R)
    | product(s(X),Y,Z) ) ).

cnf(factorial_0,axiom,
    factorial(n0,s(n0)) ).

cnf(factorial,axiom,
    ( ~ factorial(X,Z)
    | ~ product(s(X),Z,Y)
    | factorial(s(X),Y) ) ).

cnf(prove_factorial,negated_conjecture,
    ~ factorial(s(s(s(s(s(n0))))),Result) ).

%--------------------------------------------------------------------------
