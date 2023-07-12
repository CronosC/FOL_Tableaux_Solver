%--------------------------------------------------------------------------
% File     : LCL111-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Many valued sentential)
% Problem  : MV-25 depends on the Merideth system
% Version  : [McC92] axioms.
% English  : An axiomatisation of the many valued sentential calculus
%            is {MV-1,MV-2,MV-3,MV-5} by Meredith. Show that MV-25 depends
%            on the Meredith system.

% Refs     : [Ove90] Overbeek (1990), ATP competition announced at CADE-10
%          : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
%          : [Ove93] Overbeek (1993), The CADE-11 Competitions: A Personal
%          : [LM93]  Lusk & McCune (1993), Uniform Strategies: The CADE-11
% Source   : [McC92]
% Names    : CADE-11 Competition 6 [Ove90]
%          : MV-57 [MW92]
%          : THEOREM 6 [LM93]
%          : mv.in part 2 [OTTER]
%          : mv25.in [OTTER]
%          : ovb6 [SETHEO]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.1.0, 0.07 v6.0.0, 0.00 v5.5.0, 0.12 v5.4.0, 0.17 v5.3.0, 0.20 v5.2.0, 0.23 v5.1.0, 0.19 v5.0.0, 0.20 v4.0.1, 0.14 v3.4.0, 0.00 v2.4.0, 0.43 v2.3.0, 0.14 v2.2.1, 0.11 v2.2.0, 0.22 v2.1.0, 0.25 v2.0.0
% Syntax   : Number of clauses     :    6 (   5 unt;   0 nHn;   2 RR)
%            Number of literals    :    8 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   3 con; 0-2 aty)
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

cnf(prove_mv_25,negated_conjecture,
    ~ is_a_theorem(implies(implies(a,b),implies(implies(c,a),implies(c,b)))) ).

%--------------------------------------------------------------------------