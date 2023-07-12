%--------------------------------------------------------------------------
% File     : MGT030-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Earliest time point when FM growth rate exceeds EP growth rate
% Version  : [PB+94] axioms : Reduced & Augmented > Complete.
% English  : There is an earliest time point, past which FM's growth
%            rate exceeds EP's growth rate.

% Refs     : [PM93]  Peli & Masuch (1993), The Logic of Propogation Strateg
%          : [PM94]  Peli & Masuch (1994), The Logic of Propogation Strateg
%          : [Kam95] Kamps (1995), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v2.4.0
% Syntax   : Number of clauses     :   16 (   2 unt;   6 nHn;  16 RR)
%            Number of literals    :   61 (   0 equ;  40 neg)
%            Maximal clause size   :    6 (   3 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 1-4 aty)
%            Number of functors    :    8 (   8 usr;   3 con; 0-2 aty)
%            Number of variables   :   27 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT030+1.p
%--------------------------------------------------------------------------
cnf(mp_earliest_time_growth_rate_exceeds_1,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | subpopulations(first_movers,efficient_producers,A,sk1(B,A))
    | in_environment(A,sk2(A)) ) ).

cnf(mp_earliest_time_growth_rate_exceeds_2,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | greater_or_equal(sk1(B,A),B)
    | in_environment(A,sk2(A)) ) ).

cnf(mp_earliest_time_growth_rate_exceeds_3,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | subpopulations(first_movers,efficient_producers,A,sk1(B,A))
    | ~ greater(growth_rate(efficient_producers,sk2(A)),growth_rate(first_movers,sk2(A))) ) ).

cnf(mp_earliest_time_growth_rate_exceeds_4,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | subpopulations(first_movers,efficient_producers,A,sk1(B,A))
    | ~ subpopulations(first_movers,efficient_producers,A,C)
    | ~ greater(C,sk2(A))
    | greater(growth_rate(efficient_producers,C),growth_rate(first_movers,C)) ) ).

cnf(mp_earliest_time_growth_rate_exceeds_5,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | greater_or_equal(sk1(B,A),B)
    | ~ greater(growth_rate(efficient_producers,sk2(A)),growth_rate(first_movers,sk2(A))) ) ).

cnf(mp_earliest_time_growth_rate_exceeds_6,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | greater_or_equal(sk1(B,A),B)
    | ~ subpopulations(first_movers,efficient_producers,A,C)
    | ~ greater(C,sk2(A))
    | greater(growth_rate(efficient_producers,C),growth_rate(first_movers,C)) ) ).

cnf(mp_earliest_time_growth_rate_exceeds_7,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | ~ greater(growth_rate(efficient_producers,sk1(B,A)),growth_rate(first_movers,sk1(B,A)))
    | in_environment(A,sk2(A)) ) ).

cnf(mp_earliest_time_growth_rate_exceeds_8,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | ~ greater(growth_rate(efficient_producers,sk1(B,A)),growth_rate(first_movers,sk1(B,A)))
    | ~ greater(growth_rate(efficient_producers,sk2(A)),growth_rate(first_movers,sk2(A))) ) ).

cnf(mp_earliest_time_growth_rate_exceeds_9,axiom,
    ( ~ environment(A)
    | ~ in_environment(A,B)
    | ~ greater(growth_rate(efficient_producers,sk1(B,A)),growth_rate(first_movers,sk1(B,A)))
    | ~ subpopulations(first_movers,efficient_producers,A,C)
    | ~ greater(C,sk2(A))
    | greater(growth_rate(efficient_producers,C),growth_rate(first_movers,C)) ) ).

cnf(l1_10,hypothesis,
    ( ~ environment(A)
    | ~ stable(A)
    | in_environment(A,sk3(A)) ) ).

cnf(l1_11,hypothesis,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ subpopulations(first_movers,efficient_producers,A,B)
    | ~ greater_or_equal(B,sk3(A))
    | greater(growth_rate(efficient_producers,B),growth_rate(first_movers,B)) ) ).

cnf(prove_l12_12,negated_conjecture,
    environment(sk4) ).

cnf(prove_l12_13,negated_conjecture,
    stable(sk4) ).

cnf(prove_l12_14,negated_conjecture,
    ( ~ in_environment(sk4,A)
    | greater(growth_rate(efficient_producers,A),growth_rate(first_movers,A))
    | subpopulations(first_movers,efficient_producers,sk4,sk5(A)) ) ).

cnf(prove_l12_15,negated_conjecture,
    ( ~ in_environment(sk4,A)
    | greater(growth_rate(efficient_producers,A),growth_rate(first_movers,A))
    | greater(sk5(A),A) ) ).

cnf(prove_l12_16,negated_conjecture,
    ( ~ in_environment(sk4,A)
    | greater(growth_rate(efficient_producers,A),growth_rate(first_movers,A))
    | ~ greater(growth_rate(efficient_producers,sk5(A)),growth_rate(first_movers,sk5(A))) ) ).

%--------------------------------------------------------------------------
