%--------------------------------------------------------------------------
% File     : GRP132-2.002 : TPTP v8.1.2. Released v1.2.0.
% Domain   : Group Theory (Quasigroups)
% Problem  : (3,1,2) conjugate orthogonality, no idempotence
% Version  : [Sla93] axioms : Augmented.
% English  : Generate the multiplication table for the specified quasi-
%            group with 2 elements.

% Refs     : [FSB93] Fujita et al. (1993), Automatic Generation of Some Res
%          : [Sla93] Slaney (1993), Email to G. Sutcliffe
%          : [SFS95] Slaney et al. (1995), Automated Reasoning and Exhausti
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v2.1.0
% Syntax   : Number of clauses     :   13 (   6 unt;   1 nHn;  13 RR)
%            Number of literals    :   32 (   0 equ;  21 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    5 (   5 usr;   0 prp; 1-3 aty)
%            Number of functors    :    2 (   2 usr;   2 con; 0-0 aty)
%            Number of variables   :   29 (   0 sgn)
% SPC      : CNF_UNS_EPR_NEQ_NHN

% Comments : Slaney's [1993] axiomatization has been modified for this.
%          : Substitution axioms are not needed, as any positive equality
%            literals should resolve on negative ones directly.
%          : As in GRP130-1, either one of qg2_1 or qg2_2 may be used, as
%            each implies the other in this scenario, with the help of
%            cancellation. The dependence cannot be proved, so both have
%            been left in here.
%          : This version adds a simple isomorphism avoidance clause,
%            mentioned in [FSB93].
%          : tptp2X: -f tptp -s2 GRP132-2.g
%--------------------------------------------------------------------------
cnf(e_1_then_e_2,axiom,
    next(e_1,e_2) ).

cnf(e_2_greater_e_1,axiom,
    greater(e_2,e_1) ).

cnf(no_redundancy,axiom,
    ( ~ product(X,e_1,Y)
    | ~ next(X,X1)
    | ~ greater(Y,X1) ) ).

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
