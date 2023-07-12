%--------------------------------------------------------------------------
% File     : MGT036-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : First movers never outcompete efficient producers.
% Version  : [PB+94] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [PM93]  Peli & Masuch (1993), The Logic of Propogation Strateg
%          : [PM94]  Peli & Masuch (1994), The Logic of Propogation Strateg
%          : [Kam95] Kamps (1995), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v6.1.0, 0.14 v5.5.0, 0.12 v5.4.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   14 (   4 unt;   1 nHn;  12 RR)
%            Number of literals    :   38 (   0 equ;  24 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 1-4 aty)
%            Number of functors    :    7 (   7 usr;   5 con; 0-2 aty)
%            Number of variables   :   33 (   6 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT036+1.p
%--------------------------------------------------------------------------
cnf(mp_symmetry_of_FM_and_EP_1,axiom,
    ( ~ environment(A)
    | ~ subpopulations(first_movers,efficient_producers,A,B)
    | subpopulations(efficient_producers,first_movers,A,B) ) ).

cnf(mp_time_point_occur_2,axiom,
    ( ~ environment(A)
    | ~ subpopulations(first_movers,efficient_producers,A,B)
    | in_environment(A,B) ) ).

cnf(mp_growth_rate_relationships_3,axiom,
    ( environment(A)
    | ~ greater(zero,growth_rate(B,C)) ) ).

cnf(mp_growth_rate_relationships_4,axiom,
    ( subpopulations(A,B,C,D)
    | ~ greater(zero,growth_rate(A,D)) ) ).

cnf(mp_growth_rate_relationships_5,axiom,
    ( ~ greater_or_equal(growth_rate(A,B),zero)
    | ~ greater(zero,growth_rate(A,B)) ) ).

cnf(mp_growth_rate_relationships_6,axiom,
    ( greater(zero,growth_rate(A,B))
    | ~ environment(C)
    | ~ subpopulations(A,D,C,B)
    | greater_or_equal(growth_rate(A,B),zero) ) ).

cnf(d2_7,hypothesis,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | ~ greater_or_equal(growth_rate(C,D),zero)
    | ~ greater(zero,growth_rate(B,D))
    | outcompetes(C,B,D) ) ).

cnf(d2_8,hypothesis,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | ~ outcompetes(C,B,D)
    | greater_or_equal(growth_rate(C,D),zero) ) ).

cnf(d2_9,hypothesis,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | ~ outcompetes(C,B,D)
    | greater(zero,growth_rate(B,D)) ) ).

cnf(a12_10,hypothesis,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | greater(zero,growth_rate(C,B))
    | ~ greater(resilience(D),resilience(C))
    | ~ greater(zero,growth_rate(D,B)) ) ).

cnf(a2_11,hypothesis,
    greater(resilience(efficient_producers),resilience(first_movers)) ).

cnf(prove_t5_12,negated_conjecture,
    environment(sk1) ).

cnf(prove_t5_13,negated_conjecture,
    subpopulations(first_movers,efficient_producers,sk1,sk2) ).

cnf(prove_t5_14,negated_conjecture,
    outcompetes(first_movers,efficient_producers,sk2) ).

%--------------------------------------------------------------------------
