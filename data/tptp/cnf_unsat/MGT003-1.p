%--------------------------------------------------------------------------
% File     : MGT003-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Organizational death rates decrease with age.
% Version  : [PB+94] axioms.
% English  :

% Refs     : [PB+92] Peli et al. (1992), A Logical Approach to Formalizing
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam94] Kamps (1994), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   12 (   7 unt;   0 nHn;  12 RR)
%            Number of literals    :   30 (   0 equ;  19 neg)
%            Maximal clause size   :   10 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    5 (   5 usr;   0 prp; 2-3 aty)
%            Number of functors    :    6 (   6 usr;   5 con; 0-2 aty)
%            Number of variables   :   21 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT003+1.p
%--------------------------------------------------------------------------
cnf(mp4_1,axiom,
    ( ~ reorganization_free(A,B,C)
    | reorganization_free(A,B,B) ) ).

cnf(mp4_2,axiom,
    ( ~ reorganization_free(A,B,C)
    | reorganization_free(A,C,C) ) ).

cnf(mp5_3,axiom,
    ( ~ organization(A,B)
    | inertia(A,sk1(B,A),B) ) ).

cnf(t1_FOL_4,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,D)
    | ~ reorganization_free(A,B,B)
    | ~ reorganization_free(C,D,D)
    | ~ inertia(A,E,B)
    | ~ inertia(C,F,D)
    | ~ survival_chance(A,G,B)
    | ~ survival_chance(C,H,D)
    | ~ greater(F,E)
    | greater(H,G) ) ).

cnf(t2_FOL_5,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(A,C)
    | ~ reorganization_free(A,B,C)
    | ~ inertia(A,D,B)
    | ~ inertia(A,E,C)
    | ~ greater(C,B)
    | greater(E,D) ) ).

cnf(t3_FOL_6,negated_conjecture,
    organization(sk2,sk5) ).

cnf(t3_FOL_7,negated_conjecture,
    organization(sk2,sk6) ).

cnf(t3_FOL_8,negated_conjecture,
    reorganization_free(sk2,sk5,sk6) ).

cnf(t3_FOL_9,negated_conjecture,
    survival_chance(sk2,sk3,sk5) ).

cnf(t3_FOL_10,negated_conjecture,
    survival_chance(sk2,sk4,sk6) ).

cnf(t3_FOL_11,negated_conjecture,
    greater(sk6,sk5) ).

cnf(t3_FOL_12,negated_conjecture,
    ~ greater(sk4,sk3) ).

%--------------------------------------------------------------------------
