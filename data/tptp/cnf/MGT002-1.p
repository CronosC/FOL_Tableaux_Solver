%--------------------------------------------------------------------------
% File     : MGT002-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Structural inertia increases monotonically with age.
% Version  : [PB+94] axioms.
% English  :

% Refs     : [PB+92] Peli et al. (1992), A Logical Approach to Formalizing
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam94] Kamps (1994), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v8.1.0, 0.25 v7.4.0, 0.17 v7.3.0, 0.25 v6.2.0, 0.17 v6.1.0, 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   13 (   7 unt;   0 nHn;  13 RR)
%            Number of literals    :   40 (   0 equ;  28 neg)
%            Maximal clause size   :   10 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    5 (   5 usr;   0 prp; 2-3 aty)
%            Number of functors    :    6 (   6 usr;   5 con; 0-2 aty)
%            Number of variables   :   29 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT002+1.p
%--------------------------------------------------------------------------
cnf(mp3_1,axiom,
    ( ~ organization(A,B)
    | reproducibility(A,sk1(B,A),B) ) ).

cnf(mp4_2,axiom,
    ( ~ reorganization_free(A,B,C)
    | reorganization_free(A,B,B) ) ).

cnf(mp4_3,axiom,
    ( ~ reorganization_free(A,B,C)
    | reorganization_free(A,C,C) ) ).

cnf(a3_FOL_4,hypothesis,
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

cnf(a3_FOL_5,hypothesis,
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

cnf(a4_FOL_6,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(A,C)
    | ~ reorganization_free(A,B,C)
    | ~ reproducibility(A,D,B)
    | ~ reproducibility(A,E,C)
    | ~ greater(C,B)
    | greater(E,D) ) ).

cnf(t2_FOL_7,negated_conjecture,
    organization(sk2,sk5) ).

cnf(t2_FOL_8,negated_conjecture,
    organization(sk2,sk6) ).

cnf(t2_FOL_9,negated_conjecture,
    reorganization_free(sk2,sk5,sk6) ).

cnf(t2_FOL_10,negated_conjecture,
    inertia(sk2,sk3,sk5) ).

cnf(t2_FOL_11,negated_conjecture,
    inertia(sk2,sk4,sk6) ).

cnf(t2_FOL_12,negated_conjecture,
    greater(sk6,sk5) ).

cnf(t2_FOL_13,negated_conjecture,
    ~ greater(sk4,sk3) ).

%--------------------------------------------------------------------------
