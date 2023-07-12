%--------------------------------------------------------------------------
% File     : MSC002-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Miscellaneous
% Problem  : A Blind Hand Problem
% Version  : Especial.
% English  :

% Refs     : [Pop70] Popplestone (1970), Freddy, Things and Sets
%          : [MRS72] Michie et al. (1972), G-deduction
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : DBABHP [MRS72]
%          : DBABHP [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.11 v6.1.0, 0.14 v5.5.0, 0.25 v5.4.0, 0.10 v5.1.0, 0.09 v5.0.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   14 (   3 unt;   1 nHn;  10 RR)
%            Number of literals    :   30 (   0 equ;  17 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    7 (   7 usr;   0 prp; 1-3 aty)
%            Number of functors    :    7 (   7 usr;   4 con; 0-2 aty)
%            Number of variables   :   36 (   8 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The symbols are explained in [MRS72].
%--------------------------------------------------------------------------
cnf(something_is_here_now,axiom,
    at(something,here,now) ).

cnf(hand_let_go,axiom,
    ( ~ hand_at(Place,Situation)
    | hand_at(Place,let_go(Situation)) ) ).

cnf(hand_go,axiom,
    ( ~ hand_at(Place,Situation)
    | hand_at(Another_place,go(Another_place,Situation)) ) ).

cnf(cant_hold_and_let_go,axiom,
    ~ held(Thing,let_go(Situation)) ).

cnf(everything_is_red,axiom,
    ( ~ at(Thing,here,Situation)
    | red(Thing) ) ).

cnf(situation_let_go,axiom,
    ( ~ at(Thing,Place,Situation)
    | at(Thing,Place,let_go(Situation)) ) ).

cnf(situation_pick_up,axiom,
    ( ~ at(Thing,Place,Situation)
    | at(Thing,Place,pick_up(Situation)) ) ).

cnf(can_grab_if_previously_let_go,axiom,
    ( ~ at(Thing,Place,Situation)
    | grabbed(Thing,pick_up(go(Place,let_go(Situation)))) ) ).

cnf(answer_if_red_and_put_there,axiom,
    ( ~ red(Thing)
    | ~ put(Thing,there,Situation)
    | answer(Situation) ) ).

cnf(can_put_somewhere_if_grab_and_go_there,axiom,
    ( ~ at(Thing,Place,Situation)
    | ~ grabbed(Thing,Situation)
    | put(Thing,Another_place,go(Another_place,Situation)) ) ).

cnf(thing_either_held_or_went_there,axiom,
    ( held(Thing,Situation)
    | ~ at(Thing,Place,Situation)
    | at(Thing,Place,go(Another_place,Situation)) ) ).

cnf(thing_goes_in_hand,axiom,
    ( ~ hand_at(One_place,Situation)
    | ~ held(Thing,Situation)
    | at(Thing,Place,go(Place,Situation)) ) ).

cnf(thing_picked_up_by_hand,axiom,
    ( ~ hand_at(Place,Situation)
    | ~ at(Thing,Place,Situation)
    | held(Thing,pick_up(Situation)) ) ).

cnf(prove_there_is_an_answer_situation,negated_conjecture,
    ~ answer(Situation) ).

%--------------------------------------------------------------------------
