%--------------------------------------------------------------------------
% File     : MGT032-2 : TPTP v8.1.2. Released v2.4.0.
% Domain   : Management (Organisation Theory)
% Problem  : Selection favours EPs above FMs
% Version  : [PM93] axioms.
% English  : In stable environments, selection favors efficient producers
%            above first movers past a certain point in time.

% Refs     : [PM93]  Peli & Masuch (1993), The Logic of Propogation Strateg
%          : [PM94]  Peli & Masuch (1994), The Logic of Propogation Strateg
%          : [PB+94] Peli et al. (1994), A Logical Approach to Formalizing
%          : [Kam95] Kamps (1995), Email to G. Sutcliffe
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.4.0
% Syntax   : Number of clauses     :    8 (   2 unt;   0 nHn;   8 RR)
%            Number of literals    :   20 (   0 equ;  13 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    7 (   7 usr;   0 prp; 1-4 aty)
%            Number of functors    :    6 (   6 usr;   3 con; 0-2 aty)
%            Number of variables   :   10 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Created with tptp2X -f tptp -t clausify:otter MGT032+2.p
%--------------------------------------------------------------------------
cnf(mp1_high_growth_rates_1,axiom,
    ( ~ environment(A)
    | ~ subpopulations(B,C,A,D)
    | ~ greater(growth_rate(C,D),growth_rate(B,D))
    | selection_favors(C,B,D) ) ).

cnf(l1_2,hypothesis,
    ( ~ environment(A)
    | ~ stable(A)
    | in_environment(A,sk1(A)) ) ).

cnf(l1_3,hypothesis,
    ( ~ environment(A)
    | ~ stable(A)
    | ~ subpopulations(first_movers,efficient_producers,A,B)
    | ~ greater_or_equal(B,sk1(A))
    | greater(growth_rate(efficient_producers,B),growth_rate(first_movers,B)) ) ).

cnf(prove_t1_4,negated_conjecture,
    environment(sk2) ).

cnf(prove_t1_5,negated_conjecture,
    stable(sk2) ).

cnf(prove_t1_6,negated_conjecture,
    ( ~ in_environment(sk2,A)
    | subpopulations(first_movers,efficient_producers,sk2,sk3(A)) ) ).

cnf(prove_t1_7,negated_conjecture,
    ( ~ in_environment(sk2,A)
    | greater_or_equal(sk3(A),A) ) ).

cnf(prove_t1_8,negated_conjecture,
    ( ~ in_environment(sk2,A)
    | ~ selection_favors(efficient_producers,first_movers,sk3(A)) ) ).

%--------------------------------------------------------------------------
