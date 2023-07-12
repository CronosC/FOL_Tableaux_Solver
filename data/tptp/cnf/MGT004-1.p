%--------------------------------------------------------------------------
% File     : MGT004-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Attempts at reorganization increase death rates.
% Version  : [PB+94] axioms.
% English  :

% Refs     : [PB+92] Peli et al. (1992), A Logical Approach to Formalizing
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam94] Kamps (1994), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v6.3.0, 0.14 v6.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   14 (   9 unt;   2 nHn;  14 RR)
%            Number of literals    :   46 (   0 equ;  31 neg)
%            Maximal clause size   :   11 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 2-3 aty)
%            Number of functors    :    9 (   9 usr;   7 con; 0-2 aty)
%            Number of variables   :   32 (   4 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT004+1.p
%--------------------------------------------------------------------------
cnf(mp1_1,axiom,
    ( ~ organization(A,B)
    | reliability(A,sk1(B,A),B) ) ).

cnf(mp2_2,axiom,
    ( ~ organization(A,B)
    | accountability(A,sk2(B,A),B) ) ).

cnf(a1_FOL_3,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,D)
    | ~ reliability(A,E,B)
    | ~ reliability(C,F,D)
    | ~ accountability(A,G,B)
    | ~ accountability(C,H,D)
    | ~ survival_chance(A,I,B)
    | ~ survival_chance(C,J,D)
    | ~ greater(F,E)
    | ~ greater(H,G)
    | greater(J,I) ) ).

cnf(a6_FOL_4,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(A,C)
    | ~ reorganization(A,D,E)
    | ~ reliability(A,F,B)
    | ~ reliability(A,G,C)
    | ~ accountability(A,H,B)
    | ~ accountability(A,I,C)
    | greater(D,B)
    | ~ greater(C,B)
    | greater(C,E)
    | greater(F,G) ) ).

cnf(a6_FOL_5,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(A,C)
    | ~ reorganization(A,D,E)
    | ~ reliability(A,F,B)
    | ~ reliability(A,G,C)
    | ~ accountability(A,H,B)
    | ~ accountability(A,I,C)
    | greater(D,B)
    | ~ greater(C,B)
    | greater(C,E)
    | greater(H,I) ) ).

cnf(t4_FOL_6,negated_conjecture,
    organization(sk3,sk6) ).

cnf(t4_FOL_7,negated_conjecture,
    organization(sk3,sk7) ).

cnf(t4_FOL_8,negated_conjecture,
    reorganization(sk3,sk8,sk9) ).

cnf(t4_FOL_9,negated_conjecture,
    survival_chance(sk3,sk4,sk6) ).

cnf(t4_FOL_10,negated_conjecture,
    survival_chance(sk3,sk5,sk7) ).

cnf(t4_FOL_11,negated_conjecture,
    ~ greater(sk8,sk6) ).

cnf(t4_FOL_12,negated_conjecture,
    greater(sk7,sk6) ).

cnf(t4_FOL_13,negated_conjecture,
    ~ greater(sk7,sk9) ).

cnf(t4_FOL_14,negated_conjecture,
    ~ greater(sk4,sk5) ).

%--------------------------------------------------------------------------
