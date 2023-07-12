%--------------------------------------------------------------------------
% File     : MGT008-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Organizational death rates decrease with size.
% Version  : [PB+94] axioms.
% English  :

% Refs     : [PB+92] Peli et al. (1992), A Logical Approach to Formalizing
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam94] Kamps (1994), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   15 (  12 unt;   0 nHn;  15 RR)
%            Number of literals    :   34 (   0 equ;  20 neg)
%            Maximal clause size   :   10 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    7 (   7 usr;   0 prp; 2-3 aty)
%            Number of functors    :   10 (  10 usr;   9 con; 0-2 aty)
%            Number of variables   :   19 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT008+1.p
%--------------------------------------------------------------------------
cnf(mp5_1,axiom,
    ( ~ organization(A,B)
    | inertia(A,sk1(B,A),B) ) ).

cnf(a5_FOL_2,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,D)
    | ~ class(A,E,B)
    | ~ class(C,E,D)
    | ~ size(A,F,B)
    | ~ size(C,G,D)
    | ~ inertia(A,H,B)
    | ~ inertia(C,I,D)
    | ~ greater(G,F)
    | greater(I,H) ) ).

cnf(t1_FOL_3,hypothesis,
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

cnf(t8_FOL_4,negated_conjecture,
    organization(sk2,sk9) ).

cnf(t8_FOL_5,negated_conjecture,
    organization(sk3,sk10) ).

cnf(t8_FOL_6,negated_conjecture,
    reorganization_free(sk2,sk9,sk9) ).

cnf(t8_FOL_7,negated_conjecture,
    reorganization_free(sk3,sk10,sk10) ).

cnf(t8_FOL_8,negated_conjecture,
    class(sk2,sk4,sk9) ).

cnf(t8_FOL_9,negated_conjecture,
    class(sk3,sk4,sk10) ).

cnf(t8_FOL_10,negated_conjecture,
    survival_chance(sk2,sk5,sk9) ).

cnf(t8_FOL_11,negated_conjecture,
    survival_chance(sk3,sk6,sk10) ).

cnf(t8_FOL_12,negated_conjecture,
    size(sk2,sk7,sk9) ).

cnf(t8_FOL_13,negated_conjecture,
    size(sk3,sk8,sk10) ).

cnf(t8_FOL_14,negated_conjecture,
    greater(sk8,sk7) ).

cnf(t8_FOL_15,negated_conjecture,
    ~ greater(sk6,sk5) ).

%--------------------------------------------------------------------------
