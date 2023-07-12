%--------------------------------------------------------------------------
% File     : PLA003-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Planning
% Problem  : Monkey and Bananas Problem
% Version  : Especial.
% English  :

% Refs     :
% Source   : [SPRFN]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.3.0, 0.05 v5.2.0, 0.00 v2.2.1, 0.11 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   11 (   2 unt;   0 nHn;   8 RR)
%            Number of literals    :   20 (   0 equ;  10 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :   11 (  11 usr;   8 con; 0-3 aty)
%            Number of variables   :   31 (   7 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : Formulated as a state space.
%--------------------------------------------------------------------------
%----Format of a situation is
%----(monkey(loc,height,has),ladder(loc,height),bananas(loc,height))
%----can(S) means situation S is attainable

cnf(climb_up,axiom,
    ( can(monkey(Location1,ceiling,nothing),ladder(Location1,floor),Bananas)
    | ~ can(monkey(Location1,floor,nothing),ladder(Location1,floor),Bananas) ) ).

cnf(climb_down,axiom,
    ( can(monkey(Location1,floor,nothing),ladder(Location1,floor),Bananas)
    | ~ can(monkey(Location1,ceiling,nothing),ladder(Location1,floor),Bananas) ) ).

cnf(go_holding_ladder,axiom,
    ( can(monkey(Location2,floor,the_ladder),ladder(Location2,floor),Bananas)
    | ~ can(monkey(Location1,floor,the_ladder),ladder(Location1,floor),Bananas) ) ).

cnf(go_holding_bananas,axiom,
    ( can(monkey(Location2,floor,the_bananas),Ladder,bananas(Location2,floor))
    | ~ can(monkey(Location1,floor,the_bananas),Ladder,bananas(Location1,floor)) ) ).

cnf(go_holding_nothing,axiom,
    ( can(monkey(Location2,floor,nothing),Ladder,Bananas)
    | ~ can(monkey(Location1,floor,nothing),Ladder,Bananas) ) ).

cnf(drop_ladder,axiom,
    ( can(monkey(Location,Height,nothing),ladder(Location,floor),Bananas)
    | ~ can(monkey(Location,Height,the_ladder),ladder(Location,Any_height),Bananas) ) ).

cnf(drop_bananas,axiom,
    ( can(monkey(Location,Height,nothing),Ladder,bananas(Location,floor))
    | ~ can(monkey(Location,Height,the_bananas),Ladder,bananas(Location,Height)) ) ).

cnf(grab_bananas,axiom,
    ( can(monkey(Location,Height,the_bananas),Ladder,bananas(Location,Height))
    | ~ can(monkey(Location,Height,nothing),Ladder,bananas(Location,Height)) ) ).

cnf(grab_ladder,axiom,
    ( can(monkey(Location,Height,the_ladder),ladder(Location,Height),Bananas)
    | ~ can(monkey(Location,Height,nothing),ladder(Location,Height),Bananas) ) ).

cnf(initial_situation,hypothesis,
    can(monkey(l0,floor,nothing),ladder(l1,floor),bananas(l2,ceiling)) ).

cnf(prove_the_monkey_can_get_the_bananas,negated_conjecture,
    ~ can(monkey(Somewhere,Some_height,the_bananas),Ladder,What) ).

%--------------------------------------------------------------------------