%--------------------------------------------------------------------------
% File     : MSC004-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Miscellaneous
% Problem  : Show that the boy, John, has 10 fingers
% Version  : Especial.
% English  :

% Refs     : [RR+72] Reboh et al. (1972), Study of automatic theorem provin
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : HASPARTS-T2 [RR+72]
%          : HASPARTS-T2 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v5.0.0, 0.07 v4.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    8 (   2 unt;   1 nHn;   7 RR)
%            Number of literals    :   16 (   0 equ;   8 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-3 aty)
%            Number of functors    :   11 (  11 usr;   9 con; 0-5 aty)
%            Number of variables   :   14 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(not_part_inheritance,axiom,
    ( in(object_in(Big_part,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Mid_part)
    | has_parts(Big_part,times(Number_of_mid_parts,Number_of_small_parts),Small_part)
    | ~ has_parts(Big_part,Number_of_mid_parts,Mid_part) ) ).

cnf(part_inheritance,axiom,
    ( has_parts(Big_part,times(Number_of_mid_parts,Number_of_small_parts),Small_part)
    | ~ has_parts(Big_part,Number_of_mid_parts,Mid_part)
    | ~ has_parts(object_in(Big_part,Mid_part,Small_part,Number_of_mid_parts,Number_of_small_parts),Number_of_small_parts,Small_part) ) ).

cnf(john_is_a_boy,hypothesis,
    in(john,boy) ).

cnf(in_boy_in_human,hypothesis,
    ( in(X,human)
    | ~ in(X,boy) ) ).

cnf(hands_have_5_fingers,hypothesis,
    ( has_parts(X,n5,fingers)
    | ~ in(X,hand) ) ).

cnf(humans_have_two_arms,hypothesis,
    ( has_parts(X,n2,arm)
    | ~ in(X,human) ) ).

cnf(arms_have_one_hand,hypothesis,
    ( has_parts(X,n1,hand)
    | ~ in(X,arm) ) ).

cnf(prove_john_has_10_fingers,negated_conjecture,
    ~ has_parts(john,times(times(n2,n1),n5),fingers) ).

%--------------------------------------------------------------------------
