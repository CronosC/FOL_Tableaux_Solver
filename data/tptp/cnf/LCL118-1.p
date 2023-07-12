%--------------------------------------------------------------------------
% File     : LCL118-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (R)
% Problem  : YQM depends on WO
% Version  : [McC92] axioms.
% English  : Single axioms for the R calculus are QYF, YQM, WO, all
%            by Meredith and XGJ by Winker. Show that YQM depends on WO.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    : R-86 [MW92]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.08 v5.1.0, 0.06 v5.0.0, 0.07 v4.0.1, 0.00 v2.2.1, 0.11 v2.1.0, 0.25 v2.0.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
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

%----Axiom from Meredith
cnf(wo,axiom,
    is_a_theorem(equivalent(equivalent(X,equivalent(Y,Z)),equivalent(Z,equivalent(Y,X)))) ).

%----Axiom from Meredith
cnf(prove_yqm,negated_conjecture,
    ~ is_a_theorem(equivalent(equivalent(a,b),equivalent(equivalent(c,b),equivalent(c,a)))) ).

%--------------------------------------------------------------------------
