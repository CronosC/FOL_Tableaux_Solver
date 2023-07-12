%--------------------------------------------------------------------------
% File     : MSC001-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Miscellaneous
% Problem  : A Blind Hand Problem
% Version  : Especial.
% English  :

% Refs     : [Pop70] Popplestone (1970), Freddy, Things and Sets
%          : [MRS72] Michie et al. (1972), G-deduction
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : APABHP [MRS72]
%          : APABHP [WM76]

% Status   : Unsatisfiable
% Rating   : 0.14 v7.5.0, 0.33 v7.4.0, 0.00 v7.1.0, 0.33 v7.0.0, 0.38 v6.3.0, 0.14 v6.2.0, 0.11 v6.1.0, 0.14 v5.5.0, 0.12 v5.4.0, 0.10 v5.1.0, 0.09 v5.0.0, 0.07 v4.1.0, 0.00 v2.1.0, 0.12 v2.0.0
% Syntax   : Number of clauses     :   18 (   5 unt;   1 nHn;  16 RR)
%            Number of literals    :   36 (   0 equ;  21 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 1-3 aty)
%            Number of functors    :   11 (  11 usr;   7 con; 0-2 aty)
%            Number of variables   :   39 (   6 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The clauses are in the original order except that the query
%            has been put last.
%          : The symbols are explained in [MRS72].
%--------------------------------------------------------------------------
cnf(clause_1,axiom,
    ( ~ at(A,there,B)
    | ~ at(A,here,B) ) ).

cnf(clause_2,axiom,
    ~ hold(thing(A),do(let_go,B)) ).

cnf(clause_3,axiom,
    ~ red(hand) ).

cnf(clause_5,axiom,
    at(hand,A,do(go(A),B)) ).

cnf(clause_6,axiom,
    at(thing(s),here,now) ).

cnf(clause_7,axiom,
    ( ~ at(thing(A),B,do(go(B),C))
    | at(thing(A),B,C)
    | hold(thing(A),C) ) ).

cnf(clause_8,axiom,
    ( ~ at(hand,A,B)
    | ~ at(thing(C),A,B)
    | hold(thing(taken(B)),do(pick_up,B)) ) ).

cnf(clause_9,axiom,
    ( ~ hold(thing(A),B)
    | ~ at(hand,C,B)
    | at(thing(A),C,B) ) ).

cnf(clause_10,axiom,
    ( ~ hold(thing(A),B)
    | ~ at(thing(A),C,B)
    | at(hand,C,B) ) ).

cnf(clause_11,axiom,
    ( ~ red(A)
    | ~ at(A,there,B)
    | answer(B) ) ).

cnf(clause_12,axiom,
    ( ~ at(thing(A),B,C)
    | at(thing(A),B,do(go(B),C)) ) ).

cnf(clause_13,axiom,
    ( ~ hold(thing(A),B)
    | hold(thing(A),do(go(C),B)) ) ).

cnf(clause_14,axiom,
    ( ~ at(hand,A,B)
    | at(thing(taken(B)),A,B) ) ).

cnf(clause_15,axiom,
    ( ~ at(A,B,C)
    | at(A,B,do(pick_up,C)) ) ).

cnf(clause_16,axiom,
    ( ~ at(A,B,C)
    | at(A,B,do(let_go,C)) ) ).

cnf(clause_17,axiom,
    ( ~ at(A,B,do(let_go,C))
    | at(A,B,C) ) ).

cnf(things_here_now_are_red,hypothesis,
    ( ~ at(A,here,now)
    | red(A) ) ).

cnf(prove_there_is_a_red_thing,negated_conjecture,
    ~ answer(A) ).

%--------------------------------------------------------------------------
