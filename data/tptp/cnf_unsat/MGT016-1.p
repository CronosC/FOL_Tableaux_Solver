%--------------------------------------------------------------------------
% File     : MGT016-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : More complex organizations have shorter reorganization
% Version  : [PB+94] axioms.
% English  : The more complex an organization is at the beginning of
%            reorganization, the sooner disbanding due to reorganization
%            (possibly) happens - i.e., the shorter is the reorganization.

% Refs     : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam94] Kamps (1994), Email to G. Sutcliffe
%          : [Kam95] Kamps (1995), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   16 (  13 unt;   1 nHn;  16 RR)
%            Number of literals    :   38 (   0 equ;  23 neg)
%            Maximal clause size   :   13 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    7 (   7 usr;   0 prp; 2-3 aty)
%            Number of functors    :   10 (  10 usr;   9 con; 0-2 aty)
%            Number of variables   :   20 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : "Not published due to publication constraints." [Kam95].
%          : Created with tptp2X -f tptp -t clausify:otter MGT016+1.p
%--------------------------------------------------------------------------
cnf(mp5_1,axiom,
    ( ~ organization(A,B)
    | inertia(A,sk1(B,A),B) ) ).

cnf(a12_FOL_2,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,D)
    | ~ class(A,E,B)
    | ~ class(C,E,D)
    | ~ complexity(A,F,B)
    | ~ complexity(C,G,D)
    | ~ inertia(A,H,B)
    | ~ inertia(C,I,D)
    | ~ greater(G,F)
    | greater(I,H) ) ).

cnf(a14_FOL_3,hypothesis,
    ( ~ organization(A,B)
    | ~ organization(C,B)
    | organization(C,D)
    | ~ class(A,E,B)
    | ~ class(C,E,B)
    | ~ reorganization(A,B,F)
    | ~ reorganization(C,B,D)
    | ~ reorganization_type(A,G,B)
    | ~ reorganization_type(C,G,B)
    | ~ inertia(A,H,B)
    | ~ inertia(C,I,B)
    | ~ greater(I,H)
    | greater(F,D) ) ).

cnf(t16_FOL_4,negated_conjecture,
    organization(sk2,sk8) ).

cnf(t16_FOL_5,negated_conjecture,
    organization(sk3,sk8) ).

cnf(t16_FOL_6,negated_conjecture,
    ~ organization(sk3,sk10) ).

cnf(t16_FOL_7,negated_conjecture,
    class(sk2,sk5,sk8) ).

cnf(t16_FOL_8,negated_conjecture,
    class(sk3,sk5,sk8) ).

cnf(t16_FOL_9,negated_conjecture,
    reorganization(sk2,sk8,sk9) ).

cnf(t16_FOL_10,negated_conjecture,
    reorganization(sk3,sk8,sk10) ).

cnf(t16_FOL_11,negated_conjecture,
    reorganization_type(sk2,sk4,sk8) ).

cnf(t16_FOL_12,negated_conjecture,
    reorganization_type(sk3,sk4,sk8) ).

cnf(t16_FOL_13,negated_conjecture,
    complexity(sk2,sk6,sk8) ).

cnf(t16_FOL_14,negated_conjecture,
    complexity(sk3,sk7,sk8) ).

cnf(t16_FOL_15,negated_conjecture,
    greater(sk7,sk6) ).

cnf(t16_FOL_16,negated_conjecture,
    ~ greater(sk9,sk10) ).

%--------------------------------------------------------------------------
