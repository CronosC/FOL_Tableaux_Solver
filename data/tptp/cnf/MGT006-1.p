%--------------------------------------------------------------------------
% File     : MGT006-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Reliability and accountability increase with time.
% Version  : Especial.
%            Theorem formulation : Different.
% English  :

% Refs     : [PB+92] Peli et al. (1992), A Logical Approach to Formalizing
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam94] Kamps (1994), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.5.0, 0.06 v5.4.0, 0.00 v5.3.0, 0.05 v5.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   14 (   8 unt;   0 nHn;  14 RR)
%            Number of literals    :   50 (   0 equ;  37 neg)
%            Maximal clause size   :   11 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 2-3 aty)
%            Number of functors    :    8 (   8 usr;   7 con; 0-2 aty)
%            Number of variables   :   37 (   4 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Contains one less theorem predicate than [Kam94].
%          : Create with tptp2X -f tptp -t clausify:otter MGT006+1.p
%--------------------------------------------------------------------------
cnf(mp3_1,axiom,
    ( ~ organization(A,B)
    | reproducibility(A,sk1(B,A),B) ) ).

cnf(a2_FOL_2,hypothesis,
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

cnf(a2_FOL_3,hypothesis,
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

cnf(a2_FOL_4,hypothesis,
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

cnf(a4_FOL_5,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(A,C)
    | ~ reorganization_free(A,B,C)
    | ~ reproducibility(A,D,B)
    | ~ reproducibility(A,E,C)
    | ~ greater(C,B)
    | greater(E,D) ) ).

cnf(t6_FOL_6,negated_conjecture,
    organization(sk2,sk7) ).

cnf(t6_FOL_7,negated_conjecture,
    organization(sk2,sk8) ).

cnf(t6_FOL_8,negated_conjecture,
    reorganization_free(sk2,sk7,sk8) ).

cnf(t6_FOL_9,negated_conjecture,
    reliability(sk2,sk3,sk7) ).

cnf(t6_FOL_10,negated_conjecture,
    reliability(sk2,sk4,sk8) ).

cnf(t6_FOL_11,negated_conjecture,
    accountability(sk2,sk5,sk7) ).

cnf(t6_FOL_12,negated_conjecture,
    accountability(sk2,sk6,sk8) ).

cnf(t6_FOL_13,negated_conjecture,
    greater(sk8,sk7) ).

cnf(t6_FOL_14,negated_conjecture,
    ( ~ greater(sk4,sk3)
    | ~ greater(sk6,sk5) ) ).

%--------------------------------------------------------------------------
