%------------------------------------------------------------------------------
% File     : COM011-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Computing Theory
% Problem  : Problem about UNITY theory
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v5.0.0, 0.07 v4.1.0, 0.00 v4.0.0, 0.14 v3.4.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :   10 (   3 unt;   1 nHn;   9 RR)
%            Number of literals    :   20 (   0 equ;  10 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :   13 (  13 usr;   4 con; 0-3 aty)
%            Number of variables   :   27 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_0,negated_conjecture,
    c_in(v_F,c_UNITY_Oconstrains(v_A,c_union(v_A,v_B,t_a),t_a),tc_UNITY_Oprogram(t_a)) ).

cnf(cls_conjecture_1,negated_conjecture,
    c_in(v_F,c_WFair_Otransient(v_A,t_a),tc_UNITY_Oprogram(t_a)) ).

cnf(cls_conjecture_2,negated_conjecture,
    ~ c_in(v_F,c_WFair_OleadsTo(v_A,v_B,t_a),tc_UNITY_Oprogram(t_a)) ).

cnf(cls_Set_ODiffE_1,axiom,
    ( ~ c_in(V_c,c_minus(V_A,V_B,tc_set(T_a)),T_a)
    | c_in(V_c,V_A,T_a) ) ).

cnf(cls_Set_OsubsetI_0,axiom,
    ( c_in(c_Main_OsubsetI__1(V_A,V_B,T_a),V_A,T_a)
    | c_lessequals(V_A,V_B,tc_set(T_a)) ) ).

cnf(cls_Set_OsubsetI_1,axiom,
    ( ~ c_in(c_Main_OsubsetI__1(V_A,V_B,T_a),V_B,T_a)
    | c_lessequals(V_A,V_B,tc_set(T_a)) ) ).

cnf(cls_UNITY_Oconstrains__weaken__L_0,axiom,
    ( ~ c_in(V_F,c_UNITY_Oconstrains(V_A,V_A_H,T_a),tc_UNITY_Oprogram(T_a))
    | ~ c_lessequals(V_B,V_A,tc_set(T_a))
    | c_in(V_F,c_UNITY_Oconstrains(V_B,V_A_H,T_a),tc_UNITY_Oprogram(T_a)) ) ).

cnf(cls_WFair_OensuresI_0,axiom,
    ( ~ c_in(V_F,c_UNITY_Oconstrains(c_minus(V_A,V_B,tc_set(T_a)),c_union(V_A,V_B,T_a),T_a),tc_UNITY_Oprogram(T_a))
    | ~ c_in(V_F,c_WFair_Otransient(c_minus(V_A,V_B,tc_set(T_a)),T_a),tc_UNITY_Oprogram(T_a))
    | c_in(V_F,c_WFair_Oensures(V_A,V_B,T_a),tc_UNITY_Oprogram(T_a)) ) ).

cnf(cls_WFair_OleadsTo__Basis_0,axiom,
    ( ~ c_in(V_F,c_WFair_Oensures(V_A,V_B,T_a),tc_UNITY_Oprogram(T_a))
    | c_in(V_F,c_WFair_OleadsTo(V_A,V_B,T_a),tc_UNITY_Oprogram(T_a)) ) ).

cnf(cls_WFair_Otransient__strengthen_0,axiom,
    ( ~ c_in(V_F,c_WFair_Otransient(V_A,T_a),tc_UNITY_Oprogram(T_a))
    | ~ c_lessequals(V_B,V_A,tc_set(T_a))
    | c_in(V_F,c_WFair_Otransient(V_B,T_a),tc_UNITY_Oprogram(T_a)) ) ).

%------------------------------------------------------------------------------
