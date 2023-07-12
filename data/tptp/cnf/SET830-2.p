%------------------------------------------------------------------------------
% File     : SET830-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about set theory
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v7.4.0, 0.17 v7.1.0, 0.33 v7.0.0, 0.25 v6.3.0, 0.29 v6.2.0, 0.22 v6.1.0, 0.29 v5.5.0, 0.38 v5.4.0, 0.30 v5.2.0, 0.20 v5.1.0, 0.18 v5.0.0, 0.36 v4.1.0, 0.12 v4.0.1, 0.40 v4.0.0, 0.43 v3.4.0, 0.25 v3.3.0, 0.33 v3.2.0
% Syntax   : Number of clauses     :   10 (   3 unt;   1 nHn;   9 RR)
%            Number of literals    :   20 (   0 equ;  10 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :    8 (   8 usr;   5 con; 0-3 aty)
%            Number of variables   :   23 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Set_OIntE_0,axiom,
    ( ~ c_in(V_c,c_inter(V_A,V_B,T_a),T_a)
    | c_in(V_c,V_B,T_a) ) ).

cnf(cls_Set_OIntE_1,axiom,
    ( ~ c_in(V_c,c_inter(V_A,V_B,T_a),T_a)
    | c_in(V_c,V_A,T_a) ) ).

cnf(cls_Set_OIntI_0,axiom,
    ( ~ c_in(V_c,V_B,T_a)
    | ~ c_in(V_c,V_A,T_a)
    | c_in(V_c,c_inter(V_A,V_B,T_a),T_a) ) ).

cnf(cls_Set_OsubsetD_0,axiom,
    ( ~ c_in(V_c,V_A,T_a)
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | c_in(V_c,V_B,T_a) ) ).

cnf(cls_Set_OsubsetI_0,axiom,
    ( c_in(c_Main_OsubsetI__1(V_A,V_B,T_a),V_A,T_a)
    | c_lessequals(V_A,V_B,tc_set(T_a)) ) ).

cnf(cls_Set_OsubsetI_1,axiom,
    ( ~ c_in(c_Main_OsubsetI__1(V_A,V_B,T_a),V_B,T_a)
    | c_lessequals(V_A,V_B,tc_set(T_a)) ) ).

cnf(cls_conjecture_2,negated_conjecture,
    c_in(v_x,v_Y,t_a) ).

cnf(cls_conjecture_3,negated_conjecture,
    c_in(v_x,v_Z,t_a) ).

cnf(cls_conjecture_4,negated_conjecture,
    ~ c_in(v_x,v_X,t_a) ).

cnf(cls_conjecture_5,negated_conjecture,
    ( c_lessequals(V_U,v_X,tc_set(t_a))
    | ~ c_lessequals(V_U,v_Z,tc_set(t_a))
    | ~ c_lessequals(V_U,v_Y,tc_set(t_a)) ) ).

%------------------------------------------------------------------------------