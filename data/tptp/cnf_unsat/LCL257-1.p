%--------------------------------------------------------------------------
% File     : LCL257-1 : TPTP v8.1.2. Released v2.0.0.
% Domain   : Logic Calculi (Equivalential)
% Problem  : XHN depends on YQL
% Version  : [TPTP] axioms.
% English  : Show that XHN can be derived from the single Lukasiewicz
%            axiom YQL.

% Refs     : [MW92]  McCune & Wos (1992), Experiments in Automated Deductio
%          : [McC92] McCune (1992), Email to G. Sutcliffe
%          : [Wos95] Wos (1995), Searching for Circles of Pure Proofs
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.08 v5.1.0, 0.06 v5.0.0, 0.07 v4.0.1, 0.00 v2.1.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   3 con; 0-2 aty)
%            Number of variables   :    5 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : This completes the loop of single axioms' dependence in
%            problems LCL010 to LCL021.
%          : Thought to be LCLunsatisfiable.
%--------------------------------------------------------------------------
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(equivalent(X,Y))
    | ~ is_a_theorem(X)
    | is_a_theorem(Y) ) ).

%----Axiom by Lukasiewicz
cnf(yql,axiom,
    is_a_theorem(equivalent(equivalent(X,Y),equivalent(equivalent(Z,Y),equivalent(X,Z)))) ).

%----Axiom of symmetry
cnf(prove_xhn,negated_conjecture,
    ~ is_a_theorem(equivalent(x,equivalent(equivalent(y,z),equivalent(equivalent(z,x),y)))) ).

%--------------------------------------------------------------------------
