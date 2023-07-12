%--------------------------------------------------------------------------
% File     : MSC006-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Miscellaneous
% Problem  : A "non-obvious" problem
% Version  : Especial.
% English  : Suppose there are two relations, P and Q. P is transitive, and
%            Q is both transitive and symmetric. Suppose further the
%            "squareness" of P and Q: any two things are related either in
%            the P manner or the Q manner. Prove that either P is total or
%            Q is total.

% Refs     : [PR86]  Pelletier & Rudnicki (1986), Non-Obviousness
% Source   : [PR86]
% Names    : nonob.lop [SETHEO]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :    6 (   2 unt;   1 nHn;   5 RR)
%            Number of literals    :   12 (   0 equ;   7 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   4 con; 0-0 aty)
%            Number of variables   :   10 (   0 sgn)
% SPC      : CNF_UNS_EPR_NEQ_NHN

% Comments : Rudnicki says "I think that what you call the non-obvious
%            problem from our write-up with Jeff should be attributed
%            to J. \Lo\'{s} (in LaTeX)." and "J. \Lo\'{s}  is in LaTeX,
%            and it is the name of my Polish prof that told me that.
%            English approximation of his name can be typed as J. Los.".
%--------------------------------------------------------------------------
cnf(p_transitivity,hypothesis,
    ( ~ p(X,Y)
    | ~ p(Y,Z)
    | p(X,Z) ) ).

cnf(q_transitivity,hypothesis,
    ( ~ q(X,Y)
    | ~ q(Y,Z)
    | q(X,Z) ) ).

cnf(q_symmetry,hypothesis,
    ( ~ q(X,Y)
    | q(Y,X) ) ).

cnf(all_related,hypothesis,
    ( p(X,Y)
    | q(X,Y) ) ).

cnf(p_is_not_total,hypothesis,
    ~ p(a,b) ).

cnf(prove_q_is_total,negated_conjecture,
    ~ q(c,d) ).

%--------------------------------------------------------------------------
