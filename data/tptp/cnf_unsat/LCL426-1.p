%--------------------------------------------------------------------------
% File     : LCL426-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Logic Calculi (Implication)
% Problem  : Prove the mingle formula by condensed detachment
% Version  : [EF+02] axioms.
% English  : Show that the mingle axiom can be derived from the three formulas
%            given below by condensed detachment.

% Refs     : [EF+01] Ernst et al. (2001), A Concise Axiomatization of RM->
%          : [EF+02] Ernst et al. (2002), More First-order Test Problems in
% Source   : [EF+02]
% Names    : mingle-concise [EF+02]

% Status   : Unsatisfiable
% Rating   : 1.00 v2.5.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   2 RR)
%            Number of literals    :    7 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    7 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   3 con; 0-2 aty)
%            Number of variables   :   10 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : This gives a simpler basis for the system RM->
%--------------------------------------------------------------------------
%----Condensed detachment
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(implies(A,B))
    | ~ is_a_theorem(A)
    | is_a_theorem(B) ) ).

%----Suffixing
cnf(suffixing,axiom,
    is_a_theorem(implies(implies(A,B),implies(implies(B,C),implies(A,C)))) ).

%----Assertion
cnf(assertion,axiom,
    is_a_theorem(implies(A,implies(implies(A,B),B))) ).

%----Candidate
cnf(candidate,axiom,
    is_a_theorem(implies(implies(implies(implies(implies(A,B),C),implies(B,A)),C),C)) ).

%----Denial of mingle axiom
cnf(prove_mingle,negated_conjecture,
    ~ is_a_theorem(implies(implies(implies(implies(implies(a,b),b),a),c),implies(implies(implies(implies(implies(b,a),a),b),c),c))) ).

%--------------------------------------------------------------------------
