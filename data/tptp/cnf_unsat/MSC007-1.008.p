%--------------------------------------------------------------------------
% File     : MSC007-1.008 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Miscellaneous
% Problem  : Cook pigeon-hole problem
% Version  : [Pel86] axioms : Especial.
%            Theorem formulation : Propositional.
% English  : Suppose there are N holes and N+1 pigeons to put in the
%            holes. Every pigeon is in a hole and no hole contains more
%            than one pigeon. Prove that this is impossible. The size is
%            the number of pigeons.

% Refs     : [CR79]  Cook & Reckhow (1979), The Relative Efficiency of Prop
%          : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 72 (Size 4) [Pel86]
%          : pigeon.in (Size 4) [OTTER]

% Status   : Unsatisfiable
% Rating   : 0.00 v4.1.0, 0.20 v3.7.0, 0.25 v3.5.0, 0.00 v3.3.0, 0.33 v3.2.0, 0.00 v3.1.0, 0.33 v2.7.0, 0.50 v2.6.0, 0.56 v2.5.0, 0.25 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1, 0.00 v2.1.0
% Syntax   : Number of clauses     :  204 (   0 unt;   8 nHn; 204 RR)
%            Number of literals    :  448 (   0 equ; 392 neg)
%            Maximal clause size   :    7 (   2 avg)
%            Maximal term depth    :    0 (   0 avg)
%            Number of predicates  :   56 (  56 usr;  56 prp; 0-0 aty)
%            Number of functors    :    0 (   0 usr;   0 con; --- aty)
%            Number of variables   :    0 (   0 sgn)
% SPC      : CNF_UNS_PRP

% Comments : For an N hole problem, the number of propositions is N^2 + N
%            and the number of clauses is (N^3 + N^2)/2 + N+1. Thus the
%            number of propositions increases quadratically and the number
%            of clauses increases cubically.
%          : tptp2X: -f tptp -s8 MSC007-1.g
%--------------------------------------------------------------------------
cnf(pigeon_1,negated_conjecture,
    ( pigeon_1_in_hole_1
    | pigeon_1_in_hole_2
    | pigeon_1_in_hole_3
    | pigeon_1_in_hole_4
    | pigeon_1_in_hole_5
    | pigeon_1_in_hole_6
    | pigeon_1_in_hole_7 ) ).

cnf(pigeon_2,negated_conjecture,
    ( pigeon_2_in_hole_1
    | pigeon_2_in_hole_2
    | pigeon_2_in_hole_3
    | pigeon_2_in_hole_4
    | pigeon_2_in_hole_5
    | pigeon_2_in_hole_6
    | pigeon_2_in_hole_7 ) ).

cnf(pigeon_3,negated_conjecture,
    ( pigeon_3_in_hole_1
    | pigeon_3_in_hole_2
    | pigeon_3_in_hole_3
    | pigeon_3_in_hole_4
    | pigeon_3_in_hole_5
    | pigeon_3_in_hole_6
    | pigeon_3_in_hole_7 ) ).

cnf(pigeon_4,negated_conjecture,
    ( pigeon_4_in_hole_1
    | pigeon_4_in_hole_2
    | pigeon_4_in_hole_3
    | pigeon_4_in_hole_4
    | pigeon_4_in_hole_5
    | pigeon_4_in_hole_6
    | pigeon_4_in_hole_7 ) ).

cnf(pigeon_5,negated_conjecture,
    ( pigeon_5_in_hole_1
    | pigeon_5_in_hole_2
    | pigeon_5_in_hole_3
    | pigeon_5_in_hole_4
    | pigeon_5_in_hole_5
    | pigeon_5_in_hole_6
    | pigeon_5_in_hole_7 ) ).

cnf(pigeon_6,negated_conjecture,
    ( pigeon_6_in_hole_1
    | pigeon_6_in_hole_2
    | pigeon_6_in_hole_3
    | pigeon_6_in_hole_4
    | pigeon_6_in_hole_5
    | pigeon_6_in_hole_6
    | pigeon_6_in_hole_7 ) ).

cnf(pigeon_7,negated_conjecture,
    ( pigeon_7_in_hole_1
    | pigeon_7_in_hole_2
    | pigeon_7_in_hole_3
    | pigeon_7_in_hole_4
    | pigeon_7_in_hole_5
    | pigeon_7_in_hole_6
    | pigeon_7_in_hole_7 ) ).

cnf(pigeon_8,negated_conjecture,
    ( pigeon_8_in_hole_1
    | pigeon_8_in_hole_2
    | pigeon_8_in_hole_3
    | pigeon_8_in_hole_4
    | pigeon_8_in_hole_5
    | pigeon_8_in_hole_6
    | pigeon_8_in_hole_7 ) ).

cnf(hole_1_pigeons_1_and_2,negated_conjecture,
    ( ~ pigeon_1_in_hole_1
    | ~ pigeon_2_in_hole_1 ) ).

cnf(hole_1_pigeons_1_and_3,negated_conjecture,
    ( ~ pigeon_1_in_hole_1
    | ~ pigeon_3_in_hole_1 ) ).

cnf(hole_1_pigeons_1_and_4,negated_conjecture,
    ( ~ pigeon_1_in_hole_1
    | ~ pigeon_4_in_hole_1 ) ).

cnf(hole_1_pigeons_1_and_5,negated_conjecture,
    ( ~ pigeon_1_in_hole_1
    | ~ pigeon_5_in_hole_1 ) ).

cnf(hole_1_pigeons_1_and_6,negated_conjecture,
    ( ~ pigeon_1_in_hole_1
    | ~ pigeon_6_in_hole_1 ) ).

cnf(hole_1_pigeons_1_and_7,negated_conjecture,
    ( ~ pigeon_1_in_hole_1
    | ~ pigeon_7_in_hole_1 ) ).

cnf(hole_1_pigeons_1_and_8,negated_conjecture,
    ( ~ pigeon_1_in_hole_1
    | ~ pigeon_8_in_hole_1 ) ).

cnf(hole_1_pigeons_2_and_3,negated_conjecture,
    ( ~ pigeon_2_in_hole_1
    | ~ pigeon_3_in_hole_1 ) ).

cnf(hole_1_pigeons_2_and_4,negated_conjecture,
    ( ~ pigeon_2_in_hole_1
    | ~ pigeon_4_in_hole_1 ) ).

cnf(hole_1_pigeons_2_and_5,negated_conjecture,
    ( ~ pigeon_2_in_hole_1
    | ~ pigeon_5_in_hole_1 ) ).

cnf(hole_1_pigeons_2_and_6,negated_conjecture,
    ( ~ pigeon_2_in_hole_1
    | ~ pigeon_6_in_hole_1 ) ).

cnf(hole_1_pigeons_2_and_7,negated_conjecture,
    ( ~ pigeon_2_in_hole_1
    | ~ pigeon_7_in_hole_1 ) ).

cnf(hole_1_pigeons_2_and_8,negated_conjecture,
    ( ~ pigeon_2_in_hole_1
    | ~ pigeon_8_in_hole_1 ) ).

cnf(hole_1_pigeons_3_and_4,negated_conjecture,
    ( ~ pigeon_3_in_hole_1
    | ~ pigeon_4_in_hole_1 ) ).

cnf(hole_1_pigeons_3_and_5,negated_conjecture,
    ( ~ pigeon_3_in_hole_1
    | ~ pigeon_5_in_hole_1 ) ).

cnf(hole_1_pigeons_3_and_6,negated_conjecture,
    ( ~ pigeon_3_in_hole_1
    | ~ pigeon_6_in_hole_1 ) ).

cnf(hole_1_pigeons_3_and_7,negated_conjecture,
    ( ~ pigeon_3_in_hole_1
    | ~ pigeon_7_in_hole_1 ) ).

cnf(hole_1_pigeons_3_and_8,negated_conjecture,
    ( ~ pigeon_3_in_hole_1
    | ~ pigeon_8_in_hole_1 ) ).

cnf(hole_1_pigeons_4_and_5,negated_conjecture,
    ( ~ pigeon_4_in_hole_1
    | ~ pigeon_5_in_hole_1 ) ).

cnf(hole_1_pigeons_4_and_6,negated_conjecture,
    ( ~ pigeon_4_in_hole_1
    | ~ pigeon_6_in_hole_1 ) ).

cnf(hole_1_pigeons_4_and_7,negated_conjecture,
    ( ~ pigeon_4_in_hole_1
    | ~ pigeon_7_in_hole_1 ) ).

cnf(hole_1_pigeons_4_and_8,negated_conjecture,
    ( ~ pigeon_4_in_hole_1
    | ~ pigeon_8_in_hole_1 ) ).

cnf(hole_1_pigeons_5_and_6,negated_conjecture,
    ( ~ pigeon_5_in_hole_1
    | ~ pigeon_6_in_hole_1 ) ).

cnf(hole_1_pigeons_5_and_7,negated_conjecture,
    ( ~ pigeon_5_in_hole_1
    | ~ pigeon_7_in_hole_1 ) ).

cnf(hole_1_pigeons_5_and_8,negated_conjecture,
    ( ~ pigeon_5_in_hole_1
    | ~ pigeon_8_in_hole_1 ) ).

cnf(hole_1_pigeons_6_and_7,negated_conjecture,
    ( ~ pigeon_6_in_hole_1
    | ~ pigeon_7_in_hole_1 ) ).

cnf(hole_1_pigeons_6_and_8,negated_conjecture,
    ( ~ pigeon_6_in_hole_1
    | ~ pigeon_8_in_hole_1 ) ).

cnf(hole_1_pigeons_7_and_8,negated_conjecture,
    ( ~ pigeon_7_in_hole_1
    | ~ pigeon_8_in_hole_1 ) ).

cnf(hole_2_pigeons_1_and_2,negated_conjecture,
    ( ~ pigeon_1_in_hole_2
    | ~ pigeon_2_in_hole_2 ) ).

cnf(hole_2_pigeons_1_and_3,negated_conjecture,
    ( ~ pigeon_1_in_hole_2
    | ~ pigeon_3_in_hole_2 ) ).

cnf(hole_2_pigeons_1_and_4,negated_conjecture,
    ( ~ pigeon_1_in_hole_2
    | ~ pigeon_4_in_hole_2 ) ).

cnf(hole_2_pigeons_1_and_5,negated_conjecture,
    ( ~ pigeon_1_in_hole_2
    | ~ pigeon_5_in_hole_2 ) ).

cnf(hole_2_pigeons_1_and_6,negated_conjecture,
    ( ~ pigeon_1_in_hole_2
    | ~ pigeon_6_in_hole_2 ) ).

cnf(hole_2_pigeons_1_and_7,negated_conjecture,
    ( ~ pigeon_1_in_hole_2
    | ~ pigeon_7_in_hole_2 ) ).

cnf(hole_2_pigeons_1_and_8,negated_conjecture,
    ( ~ pigeon_1_in_hole_2
    | ~ pigeon_8_in_hole_2 ) ).

cnf(hole_2_pigeons_2_and_3,negated_conjecture,
    ( ~ pigeon_2_in_hole_2
    | ~ pigeon_3_in_hole_2 ) ).

cnf(hole_2_pigeons_2_and_4,negated_conjecture,
    ( ~ pigeon_2_in_hole_2
    | ~ pigeon_4_in_hole_2 ) ).

cnf(hole_2_pigeons_2_and_5,negated_conjecture,
    ( ~ pigeon_2_in_hole_2
    | ~ pigeon_5_in_hole_2 ) ).

cnf(hole_2_pigeons_2_and_6,negated_conjecture,
    ( ~ pigeon_2_in_hole_2
    | ~ pigeon_6_in_hole_2 ) ).

cnf(hole_2_pigeons_2_and_7,negated_conjecture,
    ( ~ pigeon_2_in_hole_2
    | ~ pigeon_7_in_hole_2 ) ).

cnf(hole_2_pigeons_2_and_8,negated_conjecture,
    ( ~ pigeon_2_in_hole_2
    | ~ pigeon_8_in_hole_2 ) ).

cnf(hole_2_pigeons_3_and_4,negated_conjecture,
    ( ~ pigeon_3_in_hole_2
    | ~ pigeon_4_in_hole_2 ) ).

cnf(hole_2_pigeons_3_and_5,negated_conjecture,
    ( ~ pigeon_3_in_hole_2
    | ~ pigeon_5_in_hole_2 ) ).

cnf(hole_2_pigeons_3_and_6,negated_conjecture,
    ( ~ pigeon_3_in_hole_2
    | ~ pigeon_6_in_hole_2 ) ).

cnf(hole_2_pigeons_3_and_7,negated_conjecture,
    ( ~ pigeon_3_in_hole_2
    | ~ pigeon_7_in_hole_2 ) ).

cnf(hole_2_pigeons_3_and_8,negated_conjecture,
    ( ~ pigeon_3_in_hole_2
    | ~ pigeon_8_in_hole_2 ) ).

cnf(hole_2_pigeons_4_and_5,negated_conjecture,
    ( ~ pigeon_4_in_hole_2
    | ~ pigeon_5_in_hole_2 ) ).

cnf(hole_2_pigeons_4_and_6,negated_conjecture,
    ( ~ pigeon_4_in_hole_2
    | ~ pigeon_6_in_hole_2 ) ).

cnf(hole_2_pigeons_4_and_7,negated_conjecture,
    ( ~ pigeon_4_in_hole_2
    | ~ pigeon_7_in_hole_2 ) ).

cnf(hole_2_pigeons_4_and_8,negated_conjecture,
    ( ~ pigeon_4_in_hole_2
    | ~ pigeon_8_in_hole_2 ) ).

cnf(hole_2_pigeons_5_and_6,negated_conjecture,
    ( ~ pigeon_5_in_hole_2
    | ~ pigeon_6_in_hole_2 ) ).

cnf(hole_2_pigeons_5_and_7,negated_conjecture,
    ( ~ pigeon_5_in_hole_2
    | ~ pigeon_7_in_hole_2 ) ).

cnf(hole_2_pigeons_5_and_8,negated_conjecture,
    ( ~ pigeon_5_in_hole_2
    | ~ pigeon_8_in_hole_2 ) ).

cnf(hole_2_pigeons_6_and_7,negated_conjecture,
    ( ~ pigeon_6_in_hole_2
    | ~ pigeon_7_in_hole_2 ) ).

cnf(hole_2_pigeons_6_and_8,negated_conjecture,
    ( ~ pigeon_6_in_hole_2
    | ~ pigeon_8_in_hole_2 ) ).

cnf(hole_2_pigeons_7_and_8,negated_conjecture,
    ( ~ pigeon_7_in_hole_2
    | ~ pigeon_8_in_hole_2 ) ).

cnf(hole_3_pigeons_1_and_2,negated_conjecture,
    ( ~ pigeon_1_in_hole_3
    | ~ pigeon_2_in_hole_3 ) ).

cnf(hole_3_pigeons_1_and_3,negated_conjecture,
    ( ~ pigeon_1_in_hole_3
    | ~ pigeon_3_in_hole_3 ) ).

cnf(hole_3_pigeons_1_and_4,negated_conjecture,
    ( ~ pigeon_1_in_hole_3
    | ~ pigeon_4_in_hole_3 ) ).

cnf(hole_3_pigeons_1_and_5,negated_conjecture,
    ( ~ pigeon_1_in_hole_3
    | ~ pigeon_5_in_hole_3 ) ).

cnf(hole_3_pigeons_1_and_6,negated_conjecture,
    ( ~ pigeon_1_in_hole_3
    | ~ pigeon_6_in_hole_3 ) ).

cnf(hole_3_pigeons_1_and_7,negated_conjecture,
    ( ~ pigeon_1_in_hole_3
    | ~ pigeon_7_in_hole_3 ) ).

cnf(hole_3_pigeons_1_and_8,negated_conjecture,
    ( ~ pigeon_1_in_hole_3
    | ~ pigeon_8_in_hole_3 ) ).

cnf(hole_3_pigeons_2_and_3,negated_conjecture,
    ( ~ pigeon_2_in_hole_3
    | ~ pigeon_3_in_hole_3 ) ).

cnf(hole_3_pigeons_2_and_4,negated_conjecture,
    ( ~ pigeon_2_in_hole_3
    | ~ pigeon_4_in_hole_3 ) ).

cnf(hole_3_pigeons_2_and_5,negated_conjecture,
    ( ~ pigeon_2_in_hole_3
    | ~ pigeon_5_in_hole_3 ) ).

cnf(hole_3_pigeons_2_and_6,negated_conjecture,
    ( ~ pigeon_2_in_hole_3
    | ~ pigeon_6_in_hole_3 ) ).

cnf(hole_3_pigeons_2_and_7,negated_conjecture,
    ( ~ pigeon_2_in_hole_3
    | ~ pigeon_7_in_hole_3 ) ).

cnf(hole_3_pigeons_2_and_8,negated_conjecture,
    ( ~ pigeon_2_in_hole_3
    | ~ pigeon_8_in_hole_3 ) ).

cnf(hole_3_pigeons_3_and_4,negated_conjecture,
    ( ~ pigeon_3_in_hole_3
    | ~ pigeon_4_in_hole_3 ) ).

cnf(hole_3_pigeons_3_and_5,negated_conjecture,
    ( ~ pigeon_3_in_hole_3
    | ~ pigeon_5_in_hole_3 ) ).

cnf(hole_3_pigeons_3_and_6,negated_conjecture,
    ( ~ pigeon_3_in_hole_3
    | ~ pigeon_6_in_hole_3 ) ).

cnf(hole_3_pigeons_3_and_7,negated_conjecture,
    ( ~ pigeon_3_in_hole_3
    | ~ pigeon_7_in_hole_3 ) ).

cnf(hole_3_pigeons_3_and_8,negated_conjecture,
    ( ~ pigeon_3_in_hole_3
    | ~ pigeon_8_in_hole_3 ) ).

cnf(hole_3_pigeons_4_and_5,negated_conjecture,
    ( ~ pigeon_4_in_hole_3
    | ~ pigeon_5_in_hole_3 ) ).

cnf(hole_3_pigeons_4_and_6,negated_conjecture,
    ( ~ pigeon_4_in_hole_3
    | ~ pigeon_6_in_hole_3 ) ).

cnf(hole_3_pigeons_4_and_7,negated_conjecture,
    ( ~ pigeon_4_in_hole_3
    | ~ pigeon_7_in_hole_3 ) ).

cnf(hole_3_pigeons_4_and_8,negated_conjecture,
    ( ~ pigeon_4_in_hole_3
    | ~ pigeon_8_in_hole_3 ) ).

cnf(hole_3_pigeons_5_and_6,negated_conjecture,
    ( ~ pigeon_5_in_hole_3
    | ~ pigeon_6_in_hole_3 ) ).

cnf(hole_3_pigeons_5_and_7,negated_conjecture,
    ( ~ pigeon_5_in_hole_3
    | ~ pigeon_7_in_hole_3 ) ).

cnf(hole_3_pigeons_5_and_8,negated_conjecture,
    ( ~ pigeon_5_in_hole_3
    | ~ pigeon_8_in_hole_3 ) ).

cnf(hole_3_pigeons_6_and_7,negated_conjecture,
    ( ~ pigeon_6_in_hole_3
    | ~ pigeon_7_in_hole_3 ) ).

cnf(hole_3_pigeons_6_and_8,negated_conjecture,
    ( ~ pigeon_6_in_hole_3
    | ~ pigeon_8_in_hole_3 ) ).

cnf(hole_3_pigeons_7_and_8,negated_conjecture,
    ( ~ pigeon_7_in_hole_3
    | ~ pigeon_8_in_hole_3 ) ).

cnf(hole_4_pigeons_1_and_2,negated_conjecture,
    ( ~ pigeon_1_in_hole_4
    | ~ pigeon_2_in_hole_4 ) ).

cnf(hole_4_pigeons_1_and_3,negated_conjecture,
    ( ~ pigeon_1_in_hole_4
    | ~ pigeon_3_in_hole_4 ) ).

cnf(hole_4_pigeons_1_and_4,negated_conjecture,
    ( ~ pigeon_1_in_hole_4
    | ~ pigeon_4_in_hole_4 ) ).

cnf(hole_4_pigeons_1_and_5,negated_conjecture,
    ( ~ pigeon_1_in_hole_4
    | ~ pigeon_5_in_hole_4 ) ).

cnf(hole_4_pigeons_1_and_6,negated_conjecture,
    ( ~ pigeon_1_in_hole_4
    | ~ pigeon_6_in_hole_4 ) ).

cnf(hole_4_pigeons_1_and_7,negated_conjecture,
    ( ~ pigeon_1_in_hole_4
    | ~ pigeon_7_in_hole_4 ) ).

cnf(hole_4_pigeons_1_and_8,negated_conjecture,
    ( ~ pigeon_1_in_hole_4
    | ~ pigeon_8_in_hole_4 ) ).

cnf(hole_4_pigeons_2_and_3,negated_conjecture,
    ( ~ pigeon_2_in_hole_4
    | ~ pigeon_3_in_hole_4 ) ).

cnf(hole_4_pigeons_2_and_4,negated_conjecture,
    ( ~ pigeon_2_in_hole_4
    | ~ pigeon_4_in_hole_4 ) ).

cnf(hole_4_pigeons_2_and_5,negated_conjecture,
    ( ~ pigeon_2_in_hole_4
    | ~ pigeon_5_in_hole_4 ) ).

cnf(hole_4_pigeons_2_and_6,negated_conjecture,
    ( ~ pigeon_2_in_hole_4
    | ~ pigeon_6_in_hole_4 ) ).

cnf(hole_4_pigeons_2_and_7,negated_conjecture,
    ( ~ pigeon_2_in_hole_4
    | ~ pigeon_7_in_hole_4 ) ).

cnf(hole_4_pigeons_2_and_8,negated_conjecture,
    ( ~ pigeon_2_in_hole_4
    | ~ pigeon_8_in_hole_4 ) ).

cnf(hole_4_pigeons_3_and_4,negated_conjecture,
    ( ~ pigeon_3_in_hole_4
    | ~ pigeon_4_in_hole_4 ) ).

cnf(hole_4_pigeons_3_and_5,negated_conjecture,
    ( ~ pigeon_3_in_hole_4
    | ~ pigeon_5_in_hole_4 ) ).

cnf(hole_4_pigeons_3_and_6,negated_conjecture,
    ( ~ pigeon_3_in_hole_4
    | ~ pigeon_6_in_hole_4 ) ).

cnf(hole_4_pigeons_3_and_7,negated_conjecture,
    ( ~ pigeon_3_in_hole_4
    | ~ pigeon_7_in_hole_4 ) ).

cnf(hole_4_pigeons_3_and_8,negated_conjecture,
    ( ~ pigeon_3_in_hole_4
    | ~ pigeon_8_in_hole_4 ) ).

cnf(hole_4_pigeons_4_and_5,negated_conjecture,
    ( ~ pigeon_4_in_hole_4
    | ~ pigeon_5_in_hole_4 ) ).

cnf(hole_4_pigeons_4_and_6,negated_conjecture,
    ( ~ pigeon_4_in_hole_4
    | ~ pigeon_6_in_hole_4 ) ).

cnf(hole_4_pigeons_4_and_7,negated_conjecture,
    ( ~ pigeon_4_in_hole_4
    | ~ pigeon_7_in_hole_4 ) ).

cnf(hole_4_pigeons_4_and_8,negated_conjecture,
    ( ~ pigeon_4_in_hole_4
    | ~ pigeon_8_in_hole_4 ) ).

cnf(hole_4_pigeons_5_and_6,negated_conjecture,
    ( ~ pigeon_5_in_hole_4
    | ~ pigeon_6_in_hole_4 ) ).

cnf(hole_4_pigeons_5_and_7,negated_conjecture,
    ( ~ pigeon_5_in_hole_4
    | ~ pigeon_7_in_hole_4 ) ).

cnf(hole_4_pigeons_5_and_8,negated_conjecture,
    ( ~ pigeon_5_in_hole_4
    | ~ pigeon_8_in_hole_4 ) ).

cnf(hole_4_pigeons_6_and_7,negated_conjecture,
    ( ~ pigeon_6_in_hole_4
    | ~ pigeon_7_in_hole_4 ) ).

cnf(hole_4_pigeons_6_and_8,negated_conjecture,
    ( ~ pigeon_6_in_hole_4
    | ~ pigeon_8_in_hole_4 ) ).

cnf(hole_4_pigeons_7_and_8,negated_conjecture,
    ( ~ pigeon_7_in_hole_4
    | ~ pigeon_8_in_hole_4 ) ).

cnf(hole_5_pigeons_1_and_2,negated_conjecture,
    ( ~ pigeon_1_in_hole_5
    | ~ pigeon_2_in_hole_5 ) ).

cnf(hole_5_pigeons_1_and_3,negated_conjecture,
    ( ~ pigeon_1_in_hole_5
    | ~ pigeon_3_in_hole_5 ) ).

cnf(hole_5_pigeons_1_and_4,negated_conjecture,
    ( ~ pigeon_1_in_hole_5
    | ~ pigeon_4_in_hole_5 ) ).

cnf(hole_5_pigeons_1_and_5,negated_conjecture,
    ( ~ pigeon_1_in_hole_5
    | ~ pigeon_5_in_hole_5 ) ).

cnf(hole_5_pigeons_1_and_6,negated_conjecture,
    ( ~ pigeon_1_in_hole_5
    | ~ pigeon_6_in_hole_5 ) ).

cnf(hole_5_pigeons_1_and_7,negated_conjecture,
    ( ~ pigeon_1_in_hole_5
    | ~ pigeon_7_in_hole_5 ) ).

cnf(hole_5_pigeons_1_and_8,negated_conjecture,
    ( ~ pigeon_1_in_hole_5
    | ~ pigeon_8_in_hole_5 ) ).

cnf(hole_5_pigeons_2_and_3,negated_conjecture,
    ( ~ pigeon_2_in_hole_5
    | ~ pigeon_3_in_hole_5 ) ).

cnf(hole_5_pigeons_2_and_4,negated_conjecture,
    ( ~ pigeon_2_in_hole_5
    | ~ pigeon_4_in_hole_5 ) ).

cnf(hole_5_pigeons_2_and_5,negated_conjecture,
    ( ~ pigeon_2_in_hole_5
    | ~ pigeon_5_in_hole_5 ) ).

cnf(hole_5_pigeons_2_and_6,negated_conjecture,
    ( ~ pigeon_2_in_hole_5
    | ~ pigeon_6_in_hole_5 ) ).

cnf(hole_5_pigeons_2_and_7,negated_conjecture,
    ( ~ pigeon_2_in_hole_5
    | ~ pigeon_7_in_hole_5 ) ).

cnf(hole_5_pigeons_2_and_8,negated_conjecture,
    ( ~ pigeon_2_in_hole_5
    | ~ pigeon_8_in_hole_5 ) ).

cnf(hole_5_pigeons_3_and_4,negated_conjecture,
    ( ~ pigeon_3_in_hole_5
    | ~ pigeon_4_in_hole_5 ) ).

cnf(hole_5_pigeons_3_and_5,negated_conjecture,
    ( ~ pigeon_3_in_hole_5
    | ~ pigeon_5_in_hole_5 ) ).

cnf(hole_5_pigeons_3_and_6,negated_conjecture,
    ( ~ pigeon_3_in_hole_5
    | ~ pigeon_6_in_hole_5 ) ).

cnf(hole_5_pigeons_3_and_7,negated_conjecture,
    ( ~ pigeon_3_in_hole_5
    | ~ pigeon_7_in_hole_5 ) ).

cnf(hole_5_pigeons_3_and_8,negated_conjecture,
    ( ~ pigeon_3_in_hole_5
    | ~ pigeon_8_in_hole_5 ) ).

cnf(hole_5_pigeons_4_and_5,negated_conjecture,
    ( ~ pigeon_4_in_hole_5
    | ~ pigeon_5_in_hole_5 ) ).

cnf(hole_5_pigeons_4_and_6,negated_conjecture,
    ( ~ pigeon_4_in_hole_5
    | ~ pigeon_6_in_hole_5 ) ).

cnf(hole_5_pigeons_4_and_7,negated_conjecture,
    ( ~ pigeon_4_in_hole_5
    | ~ pigeon_7_in_hole_5 ) ).

cnf(hole_5_pigeons_4_and_8,negated_conjecture,
    ( ~ pigeon_4_in_hole_5
    | ~ pigeon_8_in_hole_5 ) ).

cnf(hole_5_pigeons_5_and_6,negated_conjecture,
    ( ~ pigeon_5_in_hole_5
    | ~ pigeon_6_in_hole_5 ) ).

cnf(hole_5_pigeons_5_and_7,negated_conjecture,
    ( ~ pigeon_5_in_hole_5
    | ~ pigeon_7_in_hole_5 ) ).

cnf(hole_5_pigeons_5_and_8,negated_conjecture,
    ( ~ pigeon_5_in_hole_5
    | ~ pigeon_8_in_hole_5 ) ).

cnf(hole_5_pigeons_6_and_7,negated_conjecture,
    ( ~ pigeon_6_in_hole_5
    | ~ pigeon_7_in_hole_5 ) ).

cnf(hole_5_pigeons_6_and_8,negated_conjecture,
    ( ~ pigeon_6_in_hole_5
    | ~ pigeon_8_in_hole_5 ) ).

cnf(hole_5_pigeons_7_and_8,negated_conjecture,
    ( ~ pigeon_7_in_hole_5
    | ~ pigeon_8_in_hole_5 ) ).

cnf(hole_6_pigeons_1_and_2,negated_conjecture,
    ( ~ pigeon_1_in_hole_6
    | ~ pigeon_2_in_hole_6 ) ).

cnf(hole_6_pigeons_1_and_3,negated_conjecture,
    ( ~ pigeon_1_in_hole_6
    | ~ pigeon_3_in_hole_6 ) ).

cnf(hole_6_pigeons_1_and_4,negated_conjecture,
    ( ~ pigeon_1_in_hole_6
    | ~ pigeon_4_in_hole_6 ) ).

cnf(hole_6_pigeons_1_and_5,negated_conjecture,
    ( ~ pigeon_1_in_hole_6
    | ~ pigeon_5_in_hole_6 ) ).

cnf(hole_6_pigeons_1_and_6,negated_conjecture,
    ( ~ pigeon_1_in_hole_6
    | ~ pigeon_6_in_hole_6 ) ).

cnf(hole_6_pigeons_1_and_7,negated_conjecture,
    ( ~ pigeon_1_in_hole_6
    | ~ pigeon_7_in_hole_6 ) ).

cnf(hole_6_pigeons_1_and_8,negated_conjecture,
    ( ~ pigeon_1_in_hole_6
    | ~ pigeon_8_in_hole_6 ) ).

cnf(hole_6_pigeons_2_and_3,negated_conjecture,
    ( ~ pigeon_2_in_hole_6
    | ~ pigeon_3_in_hole_6 ) ).

cnf(hole_6_pigeons_2_and_4,negated_conjecture,
    ( ~ pigeon_2_in_hole_6
    | ~ pigeon_4_in_hole_6 ) ).

cnf(hole_6_pigeons_2_and_5,negated_conjecture,
    ( ~ pigeon_2_in_hole_6
    | ~ pigeon_5_in_hole_6 ) ).

cnf(hole_6_pigeons_2_and_6,negated_conjecture,
    ( ~ pigeon_2_in_hole_6
    | ~ pigeon_6_in_hole_6 ) ).

cnf(hole_6_pigeons_2_and_7,negated_conjecture,
    ( ~ pigeon_2_in_hole_6
    | ~ pigeon_7_in_hole_6 ) ).

cnf(hole_6_pigeons_2_and_8,negated_conjecture,
    ( ~ pigeon_2_in_hole_6
    | ~ pigeon_8_in_hole_6 ) ).

cnf(hole_6_pigeons_3_and_4,negated_conjecture,
    ( ~ pigeon_3_in_hole_6
    | ~ pigeon_4_in_hole_6 ) ).

cnf(hole_6_pigeons_3_and_5,negated_conjecture,
    ( ~ pigeon_3_in_hole_6
    | ~ pigeon_5_in_hole_6 ) ).

cnf(hole_6_pigeons_3_and_6,negated_conjecture,
    ( ~ pigeon_3_in_hole_6
    | ~ pigeon_6_in_hole_6 ) ).

cnf(hole_6_pigeons_3_and_7,negated_conjecture,
    ( ~ pigeon_3_in_hole_6
    | ~ pigeon_7_in_hole_6 ) ).

cnf(hole_6_pigeons_3_and_8,negated_conjecture,
    ( ~ pigeon_3_in_hole_6
    | ~ pigeon_8_in_hole_6 ) ).

cnf(hole_6_pigeons_4_and_5,negated_conjecture,
    ( ~ pigeon_4_in_hole_6
    | ~ pigeon_5_in_hole_6 ) ).

cnf(hole_6_pigeons_4_and_6,negated_conjecture,
    ( ~ pigeon_4_in_hole_6
    | ~ pigeon_6_in_hole_6 ) ).

cnf(hole_6_pigeons_4_and_7,negated_conjecture,
    ( ~ pigeon_4_in_hole_6
    | ~ pigeon_7_in_hole_6 ) ).

cnf(hole_6_pigeons_4_and_8,negated_conjecture,
    ( ~ pigeon_4_in_hole_6
    | ~ pigeon_8_in_hole_6 ) ).

cnf(hole_6_pigeons_5_and_6,negated_conjecture,
    ( ~ pigeon_5_in_hole_6
    | ~ pigeon_6_in_hole_6 ) ).

cnf(hole_6_pigeons_5_and_7,negated_conjecture,
    ( ~ pigeon_5_in_hole_6
    | ~ pigeon_7_in_hole_6 ) ).

cnf(hole_6_pigeons_5_and_8,negated_conjecture,
    ( ~ pigeon_5_in_hole_6
    | ~ pigeon_8_in_hole_6 ) ).

cnf(hole_6_pigeons_6_and_7,negated_conjecture,
    ( ~ pigeon_6_in_hole_6
    | ~ pigeon_7_in_hole_6 ) ).

cnf(hole_6_pigeons_6_and_8,negated_conjecture,
    ( ~ pigeon_6_in_hole_6
    | ~ pigeon_8_in_hole_6 ) ).

cnf(hole_6_pigeons_7_and_8,negated_conjecture,
    ( ~ pigeon_7_in_hole_6
    | ~ pigeon_8_in_hole_6 ) ).

cnf(hole_7_pigeons_1_and_2,negated_conjecture,
    ( ~ pigeon_1_in_hole_7
    | ~ pigeon_2_in_hole_7 ) ).

cnf(hole_7_pigeons_1_and_3,negated_conjecture,
    ( ~ pigeon_1_in_hole_7
    | ~ pigeon_3_in_hole_7 ) ).

cnf(hole_7_pigeons_1_and_4,negated_conjecture,
    ( ~ pigeon_1_in_hole_7
    | ~ pigeon_4_in_hole_7 ) ).

cnf(hole_7_pigeons_1_and_5,negated_conjecture,
    ( ~ pigeon_1_in_hole_7
    | ~ pigeon_5_in_hole_7 ) ).

cnf(hole_7_pigeons_1_and_6,negated_conjecture,
    ( ~ pigeon_1_in_hole_7
    | ~ pigeon_6_in_hole_7 ) ).

cnf(hole_7_pigeons_1_and_7,negated_conjecture,
    ( ~ pigeon_1_in_hole_7
    | ~ pigeon_7_in_hole_7 ) ).

cnf(hole_7_pigeons_1_and_8,negated_conjecture,
    ( ~ pigeon_1_in_hole_7
    | ~ pigeon_8_in_hole_7 ) ).

cnf(hole_7_pigeons_2_and_3,negated_conjecture,
    ( ~ pigeon_2_in_hole_7
    | ~ pigeon_3_in_hole_7 ) ).

cnf(hole_7_pigeons_2_and_4,negated_conjecture,
    ( ~ pigeon_2_in_hole_7
    | ~ pigeon_4_in_hole_7 ) ).

cnf(hole_7_pigeons_2_and_5,negated_conjecture,
    ( ~ pigeon_2_in_hole_7
    | ~ pigeon_5_in_hole_7 ) ).

cnf(hole_7_pigeons_2_and_6,negated_conjecture,
    ( ~ pigeon_2_in_hole_7
    | ~ pigeon_6_in_hole_7 ) ).

cnf(hole_7_pigeons_2_and_7,negated_conjecture,
    ( ~ pigeon_2_in_hole_7
    | ~ pigeon_7_in_hole_7 ) ).

cnf(hole_7_pigeons_2_and_8,negated_conjecture,
    ( ~ pigeon_2_in_hole_7
    | ~ pigeon_8_in_hole_7 ) ).

cnf(hole_7_pigeons_3_and_4,negated_conjecture,
    ( ~ pigeon_3_in_hole_7
    | ~ pigeon_4_in_hole_7 ) ).

cnf(hole_7_pigeons_3_and_5,negated_conjecture,
    ( ~ pigeon_3_in_hole_7
    | ~ pigeon_5_in_hole_7 ) ).

cnf(hole_7_pigeons_3_and_6,negated_conjecture,
    ( ~ pigeon_3_in_hole_7
    | ~ pigeon_6_in_hole_7 ) ).

cnf(hole_7_pigeons_3_and_7,negated_conjecture,
    ( ~ pigeon_3_in_hole_7
    | ~ pigeon_7_in_hole_7 ) ).

cnf(hole_7_pigeons_3_and_8,negated_conjecture,
    ( ~ pigeon_3_in_hole_7
    | ~ pigeon_8_in_hole_7 ) ).

cnf(hole_7_pigeons_4_and_5,negated_conjecture,
    ( ~ pigeon_4_in_hole_7
    | ~ pigeon_5_in_hole_7 ) ).

cnf(hole_7_pigeons_4_and_6,negated_conjecture,
    ( ~ pigeon_4_in_hole_7
    | ~ pigeon_6_in_hole_7 ) ).

cnf(hole_7_pigeons_4_and_7,negated_conjecture,
    ( ~ pigeon_4_in_hole_7
    | ~ pigeon_7_in_hole_7 ) ).

cnf(hole_7_pigeons_4_and_8,negated_conjecture,
    ( ~ pigeon_4_in_hole_7
    | ~ pigeon_8_in_hole_7 ) ).

cnf(hole_7_pigeons_5_and_6,negated_conjecture,
    ( ~ pigeon_5_in_hole_7
    | ~ pigeon_6_in_hole_7 ) ).

cnf(hole_7_pigeons_5_and_7,negated_conjecture,
    ( ~ pigeon_5_in_hole_7
    | ~ pigeon_7_in_hole_7 ) ).

cnf(hole_7_pigeons_5_and_8,negated_conjecture,
    ( ~ pigeon_5_in_hole_7
    | ~ pigeon_8_in_hole_7 ) ).

cnf(hole_7_pigeons_6_and_7,negated_conjecture,
    ( ~ pigeon_6_in_hole_7
    | ~ pigeon_7_in_hole_7 ) ).

cnf(hole_7_pigeons_6_and_8,negated_conjecture,
    ( ~ pigeon_6_in_hole_7
    | ~ pigeon_8_in_hole_7 ) ).

cnf(hole_7_pigeons_7_and_8,negated_conjecture,
    ( ~ pigeon_7_in_hole_7
    | ~ pigeon_8_in_hole_7 ) ).

%--------------------------------------------------------------------------
