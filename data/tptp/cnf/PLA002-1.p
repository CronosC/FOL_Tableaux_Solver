%--------------------------------------------------------------------------
% File     : PLA002-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Planning
% Problem  : Getting from here to there, in all weather
% Version  : Especial.
% English  : The problem is to travel from one place to another.
%            Certain paths are passable at different times of the year, so
%            a conditional plan must be generated. Either all situations
%            are cold or all situations are warm. There is a river which
%            may be crossed only in winter when it is covered with ice,
%            and a mountain range may be crossed only in summer. The
%            problem is to get from city F to city A.

% Refs     : [Pla82] Plaisted (1982), A Simplified Problem Reduction Format
% Source   : [Pla82]
% Names    : Problem 5.7 [Pla82]

% Status   : Unsatisfiable
% Rating   : 0.00 v6.3.0, 0.14 v6.2.0, 0.00 v5.0.0, 0.07 v4.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   17 (   2 unt;   1 nHn;  16 RR)
%            Number of literals    :   36 (   0 equ;  19 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 1-2 aty)
%            Number of functors    :   12 (  12 usr;   7 con; 0-2 aty)
%            Number of variables   :   17 (   3 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(warm_or_cold,hypothesis,
    ( warm(Situation1)
    | cold(Situation2) ) ).

cnf(walk_a_to_b,hypothesis,
    ( ~ at(a,Situation)
    | at(b,walk(b,Situation)) ) ).

cnf(drive_a_to_b,hypothesis,
    ( ~ at(a,Situation)
    | at(b,drive(b,Situation)) ) ).

cnf(walk_b_to_a,hypothesis,
    ( ~ at(b,Situation)
    | at(a,walk(a,Situation)) ) ).

cnf(drive_b_to_a,hypothesis,
    ( ~ at(b,Situation)
    | at(a,drive(a,Situation)) ) ).

cnf(cross_river_b_to_c,hypothesis,
    ( ~ cold(Situation)
    | ~ at(b,Situation)
    | at(c,skate(c,Situation)) ) ).

cnf(cross_river_c_to_b,hypothesis,
    ( ~ cold(Situation)
    | ~ at(c,Situation)
    | at(b,skate(b,Situation)) ) ).

cnf(climb_mountain_b_to_d,hypothesis,
    ( ~ warm(Situation)
    | ~ at(b,Situation)
    | at(d,climb(d,Situation)) ) ).

cnf(climb_mountain_d_to_b,hypothesis,
    ( ~ warm(Situation)
    | ~ at(d,Situation)
    | at(b,climb(b,Situation)) ) ).

cnf(go_c_to_d,hypothesis,
    ( ~ at(c,Situation)
    | at(d,go(d,Situation)) ) ).

cnf(go_d_to_c,hypothesis,
    ( ~ at(d,Situation)
    | at(c,go(c,Situation)) ) ).

cnf(go_c_to_e,hypothesis,
    ( ~ at(c,Situation)
    | at(e,go(e,Situation)) ) ).

cnf(go_e_to_c,hypothesis,
    ( ~ at(e,Situation)
    | at(c,go(c,Situation)) ) ).

cnf(go_d_to_f,hypothesis,
    ( ~ at(d,Situation)
    | at(f,go(f,Situation)) ) ).

cnf(go_f_to_d,hypothesis,
    ( ~ at(f,Situation)
    | at(d,go(d,Situation)) ) ).

cnf(initial,hypothesis,
    at(f,s0) ).

cnf(prove_you_can_get_to_a,negated_conjecture,
    ~ at(a,S) ).

%--------------------------------------------------------------------------
