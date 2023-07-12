%--------------------------------------------------------------------------
% File     : SYN330-1 : TPTP v8.1.2. Released v1.2.0.
% Domain   : Syntactic
% Problem  : Church problem 46.14 (2)
% Version  : Especial.
% English  :

% Refs     : [Chu56] Church (1956), Introduction to Mathematical Logic I
%          : [FL+93] Fermuller et al. (1993), Resolution Methods for the De
%          : [Tam94] Tammet (1994), Email to Geoff Sutcliffe.
% Source   : [Tam94]
% Names    : Ch14N2 [Tam94]

% Status   : Satisfiable
% Rating   : 0.00 v5.4.0, 0.33 v5.3.0, 0.29 v5.0.0, 0.38 v4.1.0, 0.43 v4.0.1, 0.29 v4.0.0, 0.25 v3.5.0, 0.29 v3.4.0, 0.50 v3.3.0, 0.33 v3.2.0, 0.20 v3.1.0, 0.29 v2.7.0, 0.00 v2.6.0, 0.25 v2.5.0, 0.33 v2.2.1, 0.50 v2.2.0, 0.67 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    8 (   0 unt;   1 nHn;   7 RR)
%            Number of literals    :   16 (   0 equ;   8 neg)
%            Maximal clause size   :    2 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    1 (   1 usr;   0 con; 2-2 aty)
%            Number of variables   :   16 (   0 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : All the problems here can be decided by using a certain
%            completeness-preserving term ordering strategies. See [FL+93].
%          : The conversion from the full 1st order form in [Chu56]
%            to clause form was done by hand by Tanel Tammet.
%--------------------------------------------------------------------------
cnf(clause1,negated_conjecture,
    ( f(X,z(X,Y))
    | ~ f(z(X,Y),Y) ) ).

cnf(clause2,negated_conjecture,
    ( ~ f(X,z(X,Y))
    | f(z(X,Y),Y) ) ).

cnf(clause3,negated_conjecture,
    ( f(z(X,Y),Y)
    | ~ f(z(X,Y),z(X,Y)) ) ).

cnf(clause4,negated_conjecture,
    ( ~ f(z(X,Y),Y)
    | f(z(X,Y),z(X,Y)) ) ).

cnf(clause5,negated_conjecture,
    ( f(X,Y)
    | ~ f(Y,X) ) ).

cnf(clause6,negated_conjecture,
    ( ~ f(Y,X)
    | f(X,Y) ) ).

cnf(clause7,negated_conjecture,
    ( f(X,Y)
    | f(X,z(X,Y)) ) ).

cnf(clause8,negated_conjecture,
    ( ~ f(X,Y)
    | ~ f(X,z(X,Y)) ) ).

%--------------------------------------------------------------------------