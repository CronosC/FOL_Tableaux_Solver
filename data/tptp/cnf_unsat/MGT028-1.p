%--------------------------------------------------------------------------
% File     : MGT028-1 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : FMs have a negative growth rate in stable environments
% Version  : [PB+94] axioms : Reduced & Augmented > Complete.
% English  : First movers have negative growth rate past a certain point
%            of time (also after the appearence of efficient producers)
%            in stable environments.

% Refs     : [PM93]  Peli & Masuch (1993), The Logic of Propogation Strateg
%          : [PM94]  Peli & Masuch (1994), The Logic of Propogation Strateg
%          : [Kam95] Kamps (1995), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :   14 (   2 unt;   4 nHn;  14 RR)
%            Number of literals    :   57 (   0 equ;  40 neg)
%            Maximal clause size   :    7 (   4 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    6 (   6 usr;   0 prp; 1-4 aty)
%            Number of functors    :   10 (  10 usr;   4 con; 0-2 aty)
%            Number of variables   :   23 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT028+1.p
%--------------------------------------------------------------------------
cnf(mp_first_movers_negative_growth_1,axiom,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ in_environment(A,B)
    | subpopulations(first_movers,efficient_producers,A,sk1(B,A))
    | greater(sk2(A),appear(efficient_producers,A)) ) ).

cnf(mp_first_movers_negative_growth_2,axiom,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ in_environment(A,B)
    | greater_or_equal(sk1(B,A),B)
    | greater(sk2(A),appear(efficient_producers,A)) ) ).

cnf(mp_first_movers_negative_growth_3,axiom,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ in_environment(A,B)
    | subpopulations(first_movers,efficient_producers,A,sk1(B,A))
    | ~ subpopulations(first_movers,efficient_producers,A,C)
    | ~ greater_or_equal(C,sk2(A))
    | greater(zero,growth_rate(first_movers,C)) ) ).

cnf(mp_first_movers_negative_growth_4,axiom,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ in_environment(A,B)
    | greater_or_equal(sk1(B,A),B)
    | ~ subpopulations(first_movers,efficient_producers,A,C)
    | ~ greater_or_equal(C,sk2(A))
    | greater(zero,growth_rate(first_movers,C)) ) ).

cnf(mp_first_movers_negative_growth_5,axiom,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ in_environment(A,B)
    | ~ greater(zero,growth_rate(first_movers,sk1(B,A)))
    | greater(sk2(A),appear(efficient_producers,A)) ) ).

cnf(mp_first_movers_negative_growth_6,axiom,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ in_environment(A,B)
    | ~ greater(zero,growth_rate(first_movers,sk1(B,A)))
    | ~ subpopulations(first_movers,efficient_producers,A,C)
    | ~ greater_or_equal(C,sk2(A))
    | greater(zero,growth_rate(first_movers,C)) ) ).

cnf(l11_7,hypothesis,
    ( ~ environment(A)
    | ~ stable(A)
    | in_environment(A,sk3(A)) ) ).

cnf(l11_8,hypothesis,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ subpopulations(first_movers,efficient_producers,A,B)
    | ~ greater_or_equal(B,sk3(A))
    | greater(growth_rate(efficient_producers,B),zero) ) ).

cnf(l11_9,hypothesis,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ subpopulations(first_movers,efficient_producers,A,B)
    | ~ greater_or_equal(B,sk3(A))
    | greater(zero,growth_rate(first_movers,B)) ) ).

cnf(prove_l10_10,negated_conjecture,
    environment(sk4) ).

cnf(prove_l10_11,negated_conjecture,
    stable(sk4) ).

cnf(prove_l10_12,negated_conjecture,
    ( ~ greater(A,appear(efficient_producers,sk4))
    | subpopulations(first_movers,efficient_producers,sk4,sk5(A)) ) ).

cnf(prove_l10_13,negated_conjecture,
    ( ~ greater(A,appear(efficient_producers,sk4))
    | greater_or_equal(sk5(A),A) ) ).

cnf(prove_l10_14,negated_conjecture,
    ( ~ greater(A,appear(efficient_producers,sk4))
    | ~ greater(zero,growth_rate(first_movers,sk5(A))) ) ).

%--------------------------------------------------------------------------
