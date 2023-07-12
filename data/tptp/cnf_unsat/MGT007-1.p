%--------------------------------------------------------------------------
% File     : MGT007-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Reproducibility decreases during reorganization.
% Version  : [PB+94] axioms.
% English  :

% Refs     : [PB+92] Peli et al. (1992), A Logical Approach to Formalizing
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam94] Kamps (1994), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   17 (   9 unt;   2 nHn;  17 RR)
%            Number of literals    :   68 (   0 equ;  50 neg)
%            Maximal clause size   :   11 (   4 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 2-3 aty)
%            Number of functors    :   10 (  10 usr;   7 con; 0-2 aty)
%            Number of variables   :   54 (   8 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT007+1.p
%--------------------------------------------------------------------------
cnf(mp1_1,axiom,
    ( ~ organization(A,B)
    | reliability(A,sk1(B,A),B) ) ).

cnf(mp2_2,axiom,
    ( ~ organization(A,B)
    | accountability(A,sk2(B,A),B) ) ).

cnf(mp_not_in_TR_3,axiom,
    ( ~ organization(A,B)
    | reproducibility(A,sk3(B,A),B) ) ).

cnf(a2_FOL_4,hypothesis,
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
    | greater(H,G) ) ).

cnf(a2_FOL_6,hypothesis,
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

cnf(a6_FOL_7,hypothesis,
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

cnf(a6_FOL_8,hypothesis,
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

cnf(t7_FOL_9,negated_conjecture,
    organization(sk4,sk7) ).

cnf(t7_FOL_10,negated_conjecture,
    organization(sk4,sk8) ).

cnf(t7_FOL_11,negated_conjecture,
    reorganization(sk4,sk9,sk10) ).

cnf(t7_FOL_12,negated_conjecture,
    reproducibility(sk4,sk5,sk7) ).

cnf(t7_FOL_13,negated_conjecture,
    reproducibility(sk4,sk6,sk8) ).

cnf(t7_FOL_14,negated_conjecture,
    ~ greater(sk9,sk7) ).

cnf(t7_FOL_15,negated_conjecture,
    greater(sk8,sk7) ).

cnf(t7_FOL_16,negated_conjecture,
    ~ greater(sk8,sk10) ).

cnf(t7_FOL_17,negated_conjecture,
    ~ greater(sk5,sk6) ).

%--------------------------------------------------------------------------
