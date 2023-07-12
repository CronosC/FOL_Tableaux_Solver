%--------------------------------------------------------------------------
% File     : GRP132-1.002 : TPTP v8.1.2. Released v1.2.0.
% Domain   : Group Theory (Quasigroups)
% Problem  : (3,1,2) conjugate orthogonality, no idempotence
% Version  : [Sla93] axioms.
% English  : Generate the multiplication table for the specified quasi-
%            group with 2 elements.

% Refs     : [FSB93] Fujita et al. (1993), Automatic Generation of Some Res
%          : [Sla93] Slaney (1993), Email to G. Sutcliffe
%          : [SFS95] Slaney et al. (1995), Automated Reasoning and Exhausti
% Source   : [Sla93]
% Names    : QG2-ni [Sla93]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.1.0
% Syntax   : Number of clauses     :   10 (   4 unt;   1 nHn;  10 RR)
%            Number of literals    :   27 (   0 equ;  18 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 1-3 aty)
%            Number of functors    :    2 (   2 usr;   2 con; 0-0 aty)
%            Number of variables   :   26 (   0 sgn)
% SPC      : CNF_UNS_EPR_NEQ_NHN

% Comments : Slaney's [1993] axiomatization has been modified for this.
%          : Substitution axioms are not needed, as any positive equality
%            literals should resolve on negative ones directly.
%          : As in GRP130-1, either one of qg2_1 or qg2_2 may be used, as
%            each implies the other in this scenario, with the help of
%            cancellation. The dependence cannot be proved, so both have
%            been left in here.
%          : tptp2X: -f tptp -s2 GRP132-1.g
%--------------------------------------------------------------------------
cnf(element_1,axiom,
    group_element(e_1) ).

cnf(element_2,axiom,
    group_element(e_2) ).

cnf(e_1_is_not_e_2,axiom,
    ~ equalish(e_1,e_2) ).

cnf(e_2_is_not_e_1,axiom,
    ~ equalish(e_2,e_1) ).

cnf(product_total_function1,axiom,
    ( ~ group_element(X)
    | ~ group_element(Y)
    | product(X,Y,e_1)
    | product(X,Y,e_2) ) ).

cnf(product_total_function2,axiom,
    ( ~ product(X,Y,W)
    | ~ product(X,Y,Z)
    | equalish(W,Z) ) ).

cnf(product_right_cancellation,axiom,
    ( ~ product(X,W,Y)
    | ~ product(X,Z,Y)
    | equalish(W,Z) ) ).

cnf(product_left_cancellation,axiom,
    ( ~ product(W,Y,X)
    | ~ product(Z,Y,X)
    | equalish(W,Z) ) ).

cnf(qg2_1,negated_conjecture,
    ( ~ product(X1,Y1,Z1)
    | ~ product(X2,Y2,Z1)
    | ~ product(Z2,X1,Y1)
    | ~ product(Z2,X2,Y2)
    | equalish(X1,X2) ) ).

cnf(qg2_2,negated_conjecture,
    ( ~ product(X1,Y1,Z1)
    | ~ product(X2,Y2,Z1)
    | ~ product(Z2,X1,Y1)
    | ~ product(Z2,X2,Y2)
    | equalish(Y1,Y2) ) ).

%--------------------------------------------------------------------------
