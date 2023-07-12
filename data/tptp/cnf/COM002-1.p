%--------------------------------------------------------------------------
% File     : COM002-1 : TPTP v8.1.2. Released v1.0.0.
% Domain   : Computing Theory
% Problem  : A program correctness theorem
% Version  : Especial.
% English  : A computing state space, with eight states - P1 to P8.
%            P1 leads to P3 via P2. There is a branch at P3 such that the
%            following state is either P4 or P6. P6 leads to P8, which has
%            a loop back to P3, while P4 leads to termination. The problem
%            is to show that there is a loop in the computation, passing
%            through P3.

% Refs     : [RR+72] Reboh et al. (1972), Study of automatic theorem provin
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : BURSTALL [RR+72]
%          : BURSTALL [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v2.2.1, 0.11 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   19 (  15 unt;   0 nHn;  19 RR)
%            Number of literals    :   25 (   0 equ;   7 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    4 (   4 usr;   0 prp; 2-2 aty)
%            Number of functors    :   22 (  22 usr;  16 con; 0-2 aty)
%            Number of variables   :   11 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : I suspect this problem was originally by R.M. Burstall.
%--------------------------------------------------------------------------
cnf(direct_success,axiom,
    ( succeeds(Goal_state,Start_state)
    | ~ follows(Goal_state,Start_state) ) ).

cnf(transitivity_of_success,axiom,
    ( succeeds(Goal_state,Start_state)
    | ~ succeeds(Goal_state,Intermediate_state)
    | ~ succeeds(Intermediate_state,Start_state) ) ).

cnf(goto_success,axiom,
    ( succeeds(Goal_state,Start_state)
    | ~ has(Start_state,goto(Label))
    | ~ labels(Label,Goal_state) ) ).

cnf(conditional_success,axiom,
    ( succeeds(Goal_state,Start_state)
    | ~ has(Start_state,ifthen(Condition,Goal_state)) ) ).

cnf(state_1,hypothesis,
    has(p1,assign(register_j,n0)) ).

cnf(transition_1_to_2,hypothesis,
    follows(p2,p1) ).

cnf(state_2,hypothesis,
    has(p2,assign(register_k,n1)) ).

cnf(label_state_3,hypothesis,
    labels(loop,p3) ).

cnf(transition_2_to_3,hypothesis,
    follows(p3,p2) ).

cnf(state_3,hypothesis,
    has(p3,ifthen(equal_function(register_j,n),p4)) ).

cnf(state_4,hypothesis,
    has(p4,goto(out)) ).

cnf(transition_4_to_5,hypothesis,
    follows(p5,p4) ).

cnf(transition_3_to_6,hypothesis,
    follows(p6,p3) ).

cnf(state_6,hypothesis,
    has(p6,assign(register_k,times(n2,register_k))) ).

cnf(transition_6_to_7,hypothesis,
    follows(p7,p6) ).

cnf(state_7,hypothesis,
    has(p7,assign(register_j,plus(register_j,n1))) ).

cnf(transition_7_to_8,hypothesis,
    follows(p8,p7) ).

cnf(state_8,hypothesis,
    has(p8,goto(loop)) ).

cnf(prove_there_is_a_loop_through_p3,negated_conjecture,
    ~ succeeds(p3,p3) ).

%--------------------------------------------------------------------------
