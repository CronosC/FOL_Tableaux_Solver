%--------------------------------------------------------------------------
% File     : PLA002-2 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Planning
% Problem  : Getting from here to there, in all weather
% Version  : Especial.
%            Theorem formulation : Augmented.
% English  :

% Refs     : [Pla82] Plaisted (1982), A Simplified Problem Reduction Format
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v7.4.0, 0.17 v7.1.0, 0.33 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.11 v6.1.0, 0.14 v5.5.0, 0.12 v5.4.0, 0.20 v5.2.0, 0.10 v5.1.0, 0.18 v5.0.0, 0.14 v4.1.0, 0.12 v4.0.1, 0.00 v2.4.0, 0.00 v2.2.1, 0.25 v2.1.0, 0.50 v2.0.0
% Syntax   : Number of clauses     :   23 (   2 unt;   1 nHn;  18 RR)
%            Number of literals    :   64 (   0 equ;  41 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 1-2 aty)
%            Number of functors    :   12 (  12 usr;   7 con; 0-2 aty)
%            Number of variables   :   27 (   5 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Includes sort information in the clauses. Inspired by the
%            problems of building a model if there is no sort info. in the
%            clauses. In this case the natural interpretation is not a
%            model of the hypotheses, as meaningless (FALSE) instances of
%            clauses can be made.
%          : Modified by Geoff Sutcliffe.
%--------------------------------------------------------------------------
cnf(warm_or_cold,hypothesis,
    ( warm(Situation1)
    | cold(Situation2)
    | ~ situation(Situation1)
    | ~ situation(Situation2) ) ).

cnf(walk_a_to_b,hypothesis,
    ( ~ at(a,Situation)
    | at(b,walk(b,Situation))
    | ~ situation(Situation) ) ).

cnf(drive_a_to_b,hypothesis,
    ( ~ at(a,Situation)
    | at(b,drive(b,Situation))
    | ~ situation(Situation) ) ).

cnf(walk_b_to_a,hypothesis,
    ( ~ at(b,Situation)
    | at(a,walk(a,Situation))
    | ~ situation(Situation) ) ).

cnf(drive_b_to_a,hypothesis,
    ( ~ at(b,Situation)
    | at(a,drive(a,Situation))
    | ~ situation(Situation) ) ).

cnf(cross_river_b_to_c,hypothesis,
    ( ~ cold(Situation)
    | ~ at(b,Situation)
    | at(c,skate(c,Situation))
    | ~ situation(Situation) ) ).

cnf(cross_river_c_to_b,hypothesis,
    ( ~ cold(Situation)
    | ~ at(c,Situation)
    | at(b,skate(b,Situation))
    | ~ situation(Situation) ) ).

cnf(climb_mountain_b_to_d,hypothesis,
    ( ~ warm(Situation)
    | ~ at(b,Situation)
    | at(d,climb(d,Situation))
    | ~ situation(Situation) ) ).

cnf(climb_mountain_d_to_b,hypothesis,
    ( ~ warm(Situation)
    | ~ at(d,Situation)
    | at(b,climb(b,Situation))
    | ~ situation(Situation) ) ).

cnf(go_c_to_d,hypothesis,
    ( ~ at(c,Situation)
    | at(d,go(d,Situation))
    | ~ situation(Situation) ) ).

cnf(go_d_to_c,hypothesis,
    ( ~ at(d,Situation)
    | at(c,go(c,Situation))
    | ~ situation(Situation) ) ).

cnf(go_c_to_e,hypothesis,
    ( ~ at(c,Situation)
    | at(e,go(e,Situation))
    | ~ situation(Situation) ) ).

cnf(go_e_to_c,hypothesis,
    ( ~ at(e,Situation)
    | at(c,go(c,Situation))
    | ~ situation(Situation) ) ).

cnf(go_d_to_f,hypothesis,
    ( ~ at(d,Situation)
    | at(f,go(f,Situation))
    | ~ situation(Situation) ) ).

cnf(go_f_to_d,hypothesis,
    ( ~ at(f,Situation)
    | at(d,go(d,Situation))
    | ~ situation(Situation) ) ).

cnf(initial_situation,hypothesis,
    situation(s0) ).

cnf(walk_situation,hypothesis,
    ( ~ situation(Situation)
    | situation(walk(Somewhere,Situation)) ) ).

cnf(drive_situation,hypothesis,
    ( ~ situation(Situation)
    | situation(drive(Somewhere,Situation)) ) ).

cnf(climb_situation,hypothesis,
    ( ~ situation(Situation)
    | situation(climb(Somewhere,Situation)) ) ).

cnf(skate_situation,hypothesis,
    ( ~ situation(Situation)
    | situation(skate(Somewhere,Situation)) ) ).

cnf(go_situation,hypothesis,
    ( ~ situation(Situation)
    | situation(go(Somewhere,Situation)) ) ).

cnf(initial,hypothesis,
    at(f,s0) ).

cnf(prove_you_can_get_to_a_in_a_situation,negated_conjecture,
    ( ~ at(a,S)
    | ~ situation(S) ) ).

%--------------------------------------------------------------------------
