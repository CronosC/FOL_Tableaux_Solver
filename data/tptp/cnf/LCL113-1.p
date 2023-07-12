%--------------------------------------------------------------------------
% File     : LCL113-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Many valued sentential)
% Problem  : MV-33 depnds on the Merideth system
% Version  : [McC92] axioms.
% English  : An axiomatisation of the many valued sentential calculus
%            is {MV-1,MV-2,MV-3,MV-5} by Meredith. Show that 33 depends
%            on the Meredith system.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
% Source   : [McC92]
% Names    : MV-59 [MW92]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.1.0, 0.29 v6.0.0, 0.00 v5.5.0, 0.38 v5.4.0, 0.39 v5.3.0, 0.50 v5.2.0, 0.31 v5.1.0, 0.44 v5.0.0, 0.33 v4.1.0, 0.47 v4.0.1, 0.14 v3.4.0, 0.00 v3.1.0, 0.17 v2.7.0, 0.38 v2.6.0, 0.29 v2.5.0, 0.14 v2.4.0, 0.29 v2.3.0, 0.29 v2.2.1, 0.78 v2.1.0, 0.88 v2.0.0
% Syntax   : Number of clauses     :    6 (   5 unt;   0 nHn;   2 RR)
%            Number of literals    :    8 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   2 con; 0-2 aty)
%            Number of variables   :   11 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(mv_1,axiom,
    is_a_theorem(implies(X,implies(Y,X))) ).

cnf(mv_2,axiom,
    is_a_theorem(implies(implies(X,Y),implies(implies(Y,Z),implies(X,Z)))) ).

cnf(mv_3,axiom,
    is_a_theorem(implies(implies(implies(X,Y),Y),implies(implies(Y,X),X))) ).

cnf(mv_5,axiom,
    is_a_theorem(implies(implies(not(X),not(Y)),implies(Y,X))) ).

cnf(prove_mv_33,negated_conjecture,
    ~ is_a_theorem(implies(implies(not(a),b),implies(not(b),a))) ).

%--------------------------------------------------------------------------
