%--------------------------------------------------------------------------
% File     : LCL017-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Equivalential)
% Problem  : YRO depends on PYO
% Version  : [McC92] axioms.
% English  : Show that the single Meredith axiom YRO can be derived from
%            the single Meredith axiom PYO.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
%          : [Wos95] Wos (1995), Searching for Circles of Pure Proofs
% Source   : [McC92]
% Names    : EC-80 [MW92]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.17 v7.3.0, 0.00 v6.2.0, 0.17 v6.1.0, 0.43 v6.0.0, 0.11 v5.5.0, 0.50 v5.4.0, 0.56 v5.3.0, 0.65 v5.2.0, 0.46 v5.1.0, 0.56 v5.0.0, 0.53 v4.0.1, 0.29 v3.4.0, 0.20 v3.3.0, 0.00 v3.1.0, 0.33 v2.7.0, 0.50 v2.6.0, 0.43 v2.5.0, 0.29 v2.4.0, 0.43 v2.3.0, 0.43 v2.2.1, 0.67 v2.2.0, 0.78 v2.1.0, 0.88 v2.0.0
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

%----Axiom by Meredith
cnf(pyo,axiom,
    is_a_theorem(equivalent(equivalent(equivalent(X,equivalent(Y,Z)),Z),equivalent(Y,X))) ).

%----Axiom by Meredith
cnf(prove_yro,negated_conjecture,
    ~ is_a_theorem(equivalent(equivalent(a,b),equivalent(c,equivalent(equivalent(c,b),a)))) ).

%--------------------------------------------------------------------------
