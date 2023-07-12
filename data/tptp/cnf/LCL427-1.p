%--------------------------------------------------------------------------
% File     : LCL427-1 : TPTP v8.1.2. Released v2.5.0.
% Domain   : Logic Calculi
% Problem  : ORG-D23 is a single axiom for propositional calculus
% Version  : [EF+02] axioms.
% English  : Show that formula ORG-D23 is a single axiom for propositional
%            calculus in terms of the Sheffer stroke by deriving Nicod's
%            single axiom.

% Refs     : [EF+02] Ernst et al. (2002), More First-order Test Problems in
% Source   : [EF+02]
% Names    : sheffer-org-d23 [EF+02]

% Status   : Unsatisfiable
% Rating   : 1.00 v2.5.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    5 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 1-1 aty)
%            Number of functors    :    6 (   6 usr;   5 con; 0-2 aty)
%            Number of variables   :    7 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The nice property of ORG-D23 is that it is organic; that is, no
%            subformula is a theorem.
%--------------------------------------------------------------------------
%----Detachment rule for the Sheffer stroke
cnf(condensed_detachment,axiom,
    ( ~ is_a_theorem(detach(A,detach(B,C)))
    | ~ is_a_theorem(A)
    | is_a_theorem(C) ) ).

%----ORG-D23
cnf(org_d23,axiom,
    is_a_theorem(detach(detach(A,detach(B,C)),detach(detach(A,detach(B,C)),detach(detach(D,C),detach(detach(C,D),detach(A,D)))))) ).

%----Denial of Nicod's original single axiom
cnf(prove_nicod,negated_conjecture,
    ~ is_a_theorem(detach(detach(a,detach(b,c)),detach(detach(e,detach(e,e)),detach(detach(f,b),detach(detach(a,f),detach(a,f)))))) ).

%--------------------------------------------------------------------------
