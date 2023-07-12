%--------------------------------------------------------------------------
% File     : MGT022-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Decreasing resource availability affects FMS more than EPs
% Version  : [PB+94] axioms.
% English  : Decreasing resource availability affects the disbanding rate
%            of first movers more than the disbanding rate of efficient
%            producers.

% Refs     : [PM93]  Peli & Masuch (1993), The Logic of Propogation Strateg
%          : [PM94]  Peli & Masuch (1994), The Logic of Propogation Strateg
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam95] Kamps (1995), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v2.4.0
% Syntax   : Number of clauses     :   10 (   3 unt;   2 nHn;  10 RR)
%            Number of literals    :   23 (   0 equ;  12 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 1-4 aty)
%            Number of functors    :    8 (   8 usr;   4 con; 0-2 aty)
%            Number of variables   :    9 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Same as version with [PM93] axioms.
%          : Created with tptp2X -f tptp -t clausify:otter MGT022+1.p
%--------------------------------------------------------------------------
cnf(mp_constant_not_decrease_1,axiom,
    ( ~ constant(A)
    | ~ decreases(A) ) ).

cnf(a5_2,hypothesis,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | ~ greater(resilience(C),resilience(B))
    | ~ decreases(resources(A,D))
    | increases(difference(disbanding_rate(B,D),disbanding_rate(C,D))) ) ).

cnf(a5_3,hypothesis,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | ~ greater(resilience(C),resilience(B))
    | ~ constant(resources(A,D))
    | constant(difference(disbanding_rate(B,D),disbanding_rate(C,D))) ) ).

cnf(a2_4,hypothesis,
    greater(resilience(efficient_producers),resilience(first_movers)) ).

cnf(prove_l4_5,negated_conjecture,
    environment(sk1) ).

cnf(prove_l4_6,negated_conjecture,
    subpopulations(first_movers,efficient_producers,sk1,sk2) ).

cnf(prove_l4_7,negated_conjecture,
    ( decreases(resources(sk1,sk2))
    | constant(resources(sk1,sk2)) ) ).

cnf(prove_l4_8,negated_conjecture,
    ( decreases(resources(sk1,sk2))
    | decreases(difference(disbanding_rate(first_movers,sk2),disbanding_rate(efficient_producers,sk2))) ) ).

cnf(prove_l4_9,negated_conjecture,
    ( ~ increases(difference(disbanding_rate(first_movers,sk2),disbanding_rate(efficient_producers,sk2)))
    | constant(resources(sk1,sk2)) ) ).

cnf(prove_l4_10,negated_conjecture,
    ( ~ increases(difference(disbanding_rate(first_movers,sk2),disbanding_rate(efficient_producers,sk2)))
    | decreases(difference(disbanding_rate(first_movers,sk2),disbanding_rate(efficient_producers,sk2))) ) ).

%--------------------------------------------------------------------------
