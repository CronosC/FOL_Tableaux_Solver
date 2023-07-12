%--------------------------------------------------------------------------
% File     : LCL168-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Equivalential)
% Problem  : XEH is not a single axiom for the R-calculus
% Version  : [WW+90] axioms.
% English  : To show that XEH is not a single axiom, attempt to derive
%            from it any one of YQM, WO, XGJ or QYF, which are known
%            single axioms.

% Refs     : [WW+90] Wos et al. (1990), Automated Reasoning Contributes to
%          : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
% Source   : [WW+90]
% Names    : RC-2 [WW+90]

% Status   : Satisfiable
% Rating   : 0.00 v8.1.0, 0.33 v7.5.0, 0.00 v6.2.0, 0.20 v6.1.0, 0.67 v5.5.0, 0.75 v5.4.0, 0.89 v5.3.0, 0.86 v5.0.0, 0.62 v4.1.0, 0.57 v4.0.0, 0.62 v3.5.0, 0.71 v3.4.0, 0.83 v3.2.0, 0.80 v3.1.0, 0.86 v2.7.0, 0.80 v2.6.0, 0.75 v2.5.0, 0.83 v2.4.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :    6 (   5 unt;   0 nHn;   5 RR)
%            Number of literals    :    8 (   0 equ;   6 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   3 con; 0-2 aty)
%            Number of variables   :    5 (   0 sgn)
% SPC      : CNF_SAT_RFO_NEQ

% Comments : This is not how the problem is attacked in [WW+90].
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(equivalent(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(xeh,axiom,
    is_a_theorem(equivalent(X,equivalent(equivalent(Y,equivalent(equivalent(Y,Z),X)),Z))) ).

%----Axiom from Meredith
cnf(try_prove_qyf,negated_conjecture,
    ~ is_a_theorem(equivalent(equivalent(equivalent(a,b),equivalent(a,c)),equivalent(c,b))) ).

%----Axiom from Meredith
cnf(try_prove_yqm,negated_conjecture,
    ~ is_a_theorem(equivalent(equivalent(a,b),equivalent(equivalent(c,b),equivalent(c,a)))) ).

%----Axiom from Meredith
cnf(try_prove_wo,negated_conjecture,
    ~ is_a_theorem(equivalent(equivalent(a,equivalent(b,c)),equivalent(c,equivalent(b,a)))) ).

%----Axiom from Winker
cnf(try_prove_xgj,negated_conjecture,
    ~ is_a_theorem(equivalent(a,equivalent(equivalent(b,equivalent(c,a)),equivalent(b,c)))) ).

%--------------------------------------------------------------------------
