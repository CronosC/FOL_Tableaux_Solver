%--------------------------------------------------------------------------
% File     : MGT001-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Selection favors organizations with high inertia
% Version  : [PB+94] axioms.
% English  : Selection within populations of organizations in modern
%            societies favours organizations whose structure have high
%            inertia.

% Refs     : [PB+92] Peli et al. (1992), A Logical Approach to Formalizing
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam94] Kamps (1994), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   19 (  10 unt;   0 nHn;  19 RR)
%            Number of literals    :   78 (   0 equ;  60 neg)
%            Maximal clause size   :   11 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    8 (   8 usr;   0 prp; 2-3 aty)
%            Number of functors    :   11 (  11 usr;   8 con; 0-2 aty)
%            Number of variables   :   62 (   4 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT001+1.p
%--------------------------------------------------------------------------
cnf(mp1_1,axiom,
    ( ~ organization(A,B)
    | reliability(A,sk1(B,A),B) ) ).

cnf(mp2_2,axiom,
    ( ~ organization(A,B)
    | accountability(A,sk2(B,A),B) ) ).

cnf(mp3_3,axiom,
    ( ~ organization(A,B)
    | reproducibility(A,sk3(B,A),B) ) ).

cnf(a1_FOL_4,hypothesis,
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

cnf(a2_FOL_5,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,D)
    | ~ reliability(A,E,B)
    | ~ reliability(C,F,D)
    | ~ accountability(A,G,B)
    | ~ accountability(C,H,D)
    | ~ reproducibility(A,I,B)
    | ~ reproducibility(C,J,D)
    | ~ greater(J,I)
    | greater(F,E) ) ).

cnf(a2_FOL_6,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,D)
    | ~ reliability(A,E,B)
    | ~ reliability(C,F,D)
    | ~ accountability(A,G,B)
    | ~ accountability(C,H,D)
    | ~ reproducibility(A,I,B)
    | ~ reproducibility(C,J,D)
    | ~ greater(J,I)
    | greater(H,G) ) ).

cnf(a2_FOL_7,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,D)
    | ~ reliability(A,E,B)
    | ~ reliability(C,F,D)
    | ~ accountability(A,G,B)
    | ~ accountability(C,H,D)
    | ~ reproducibility(A,I,B)
    | ~ reproducibility(C,J,D)
    | ~ greater(F,E)
    | ~ greater(H,G)
    | greater(J,I) ) ).

cnf(a3_FOL_8,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,D)
    | ~ reorganization_free(A,B,B)
    | ~ reorganization_free(C,D,D)
    | ~ reproducibility(A,E,B)
    | ~ reproducibility(C,F,D)
    | ~ inertia(A,G,B)
    | ~ inertia(C,H,D)
    | ~ greater(F,E)
    | greater(H,G) ) ).

cnf(a3_FOL_9,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,D)
    | ~ reorganization_free(A,B,B)
    | ~ reorganization_free(C,D,D)
    | ~ reproducibility(A,E,B)
    | ~ reproducibility(C,F,D)
    | ~ inertia(A,G,B)
    | ~ inertia(C,H,D)
    | ~ greater(H,G)
    | greater(F,E) ) ).

cnf(t1_FOL_10,negated_conjecture,
    organization(sk4,sk6) ).

cnf(t1_FOL_11,negated_conjecture,
    organization(sk5,sk7) ).

cnf(t1_FOL_12,negated_conjecture,
    reorganization_free(sk4,sk6,sk6) ).

cnf(t1_FOL_13,negated_conjecture,
    reorganization_free(sk5,sk7,sk7) ).

cnf(t1_FOL_14,negated_conjecture,
    inertia(sk4,sk8,sk6) ).

cnf(t1_FOL_15,negated_conjecture,
    inertia(sk5,sk9,sk7) ).

cnf(t1_FOL_16,negated_conjecture,
    survival_chance(sk4,sk10,sk6) ).

cnf(t1_FOL_17,negated_conjecture,
    survival_chance(sk5,sk11,sk7) ).

cnf(t1_FOL_18,negated_conjecture,
    greater(sk9,sk8) ).

cnf(t1_FOL_19,negated_conjecture,
    ~ greater(sk11,sk10) ).

%--------------------------------------------------------------------------
