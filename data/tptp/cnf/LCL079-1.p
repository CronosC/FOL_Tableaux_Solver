%--------------------------------------------------------------------------
% File     : LCL079-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Logic Calculi (Implication/Negation 2 valued sentential)
% Problem  : Transitivity can be derived from Church's system
% Version  : [ANL] axioms.
% English  : An axiomatisation of the Implication/Negation 2 valued
%            sentential calculus is {CN-18,CN-35,CN-49} by Church. Show
%            that transitivity of implies can be derived from the Church
%            system.

% Refs     :
% Source   : [ANL]
% Names    : morgan.one.ver2.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.05 v5.2.0, 0.00 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    7 (   6 unt;   0 nHn;   4 RR)
%            Number of literals    :    9 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    5 (   5 usr;   3 con; 0-2 aty)
%            Number of variables   :    9 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Contributed to the ANL library by Charles Morgan.
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

cnf(cn_18,axiom,
    is_a_theorem(implies(X,implies(Y,X))) ).

cnf(cn_35,axiom,
    is_a_theorem(implies(implies(X,implies(Y,Z)),implies(implies(X,Y),implies(X,Z)))) ).

cnf(cn_49_reversed,axiom,
    is_a_theorem(implies(implies(Y,X),implies(not(X),not(Y)))) ).

cnf(a_implies_b,hypothesis,
    is_a_theorem(implies(a,b)) ).

cnf(b_implies_c,hypothesis,
    is_a_theorem(implies(b,c)) ).

cnf(prove_transitivity,negated_conjecture,
    ~ is_a_theorem(implies(a,c)) ).

%--------------------------------------------------------------------------
