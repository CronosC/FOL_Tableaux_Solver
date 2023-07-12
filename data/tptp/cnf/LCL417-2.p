%--------------------------------------------------------------------------
% File     : LCL417-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Logic Calculi (Equivalential)
% Problem  : XCB is a single axiom for the equivalential calculus
% Version  : [McC05] axioms.
% English  : Show that formula XCB is a single axiom for the equivalential
%            calculus by deriving the pair of axioms {symmetry, transitivity}.

% Refs     : [McC05] McCune (2005), Fascinating XCB Inference
%          : [WUF02] Wos et al. (2002), Vanquishing the XCB Question: The M
% Source   : [McC05]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.57 v8.1.0, 0.50 v7.4.0, 0.83 v7.3.0, 0.75 v7.0.0, 1.00 v3.2.0
% Syntax   : Number of clauses     :    3 (   1 unt;   0 nHn;   2 RR)
%            Number of literals    :    6 (   0 equ;   4 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    5 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    4 (   4 usr;   3 con; 0-2 aty)
%            Number of variables   :    5 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments :
%--------------------------------------------------------------------------
%----Condensed detachment
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(equivalent(A,B))
    | ~ is_a_theorem(A)
    | is_a_theorem(B) ) ).

%----XCB
cnf(xcb,axiom,
    is_a_theorem(equivalent(A,equivalent(equivalent(equivalent(A,B),equivalent(C,B)),C))) ).

%----Denial of the pair of axioms {symmetry, transitivity}
cnf(prove_symmetry_and_transitivity,negated_conjecture,
    ( ~ is_a_theorem(equivalent(equivalent(a,b),equivalent(b,a)))
    | ~ is_a_theorem(equivalent(equivalent(a,b),equivalent(equivalent(b,c),equivalent(a,c)))) ) ).

%--------------------------------------------------------------------------
