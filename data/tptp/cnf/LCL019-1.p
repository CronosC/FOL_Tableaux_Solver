%--------------------------------------------------------------------------
% File     : LCL019-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Equivalential)
% Problem  : PYM depends on XGK
% Version  : [McC92] axioms.
% English  : Show that the single Meredith axiom PYM can be derived from
%            the single Kalman axiom XGK.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
%          : [Wos95] Wos (1995), Searching for Circles of Pure Proofs
% Source   : [McC92]
% Names    : EC-82 [MW92]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0, 0.00 v6.2.0, 0.33 v6.1.0, 0.57 v6.0.0, 0.22 v5.5.0, 0.56 v5.4.0, 0.67 v5.3.0, 0.75 v5.2.0, 0.62 v5.1.0, 0.69 v5.0.0, 0.67 v4.0.1, 0.43 v4.0.0, 0.29 v3.4.0, 0.20 v3.3.0, 0.00 v3.2.0, 0.33 v2.7.0, 0.50 v2.6.0, 0.57 v2.5.0, 0.71 v2.4.0, 0.57 v2.3.0, 0.43 v2.2.1, 0.78 v2.2.0, 0.89 v2.1.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   3 con; 0-2 aty)
%            Number of variables   :    5 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(equivalent(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

%----Axiom by Kalman
cnf(xgk,axiom,
    is_a_theorem(equivalent(X,equivalent(equivalent(Y,equivalent(Z,X)),equivalent(Z,Y)))) ).

%----Axiom by Meredith
cnf(prove_pym,negated_conjecture,
    ~ is_a_theorem(equivalent(equivalent(equivalent(a,equivalent(b,c)),b),equivalent(c,a))) ).

%--------------------------------------------------------------------------