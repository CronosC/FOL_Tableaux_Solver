%------------------------------------------------------------------------------
% File     : SET863-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.1.0, 0.17 v7.0.0, 0.25 v6.4.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v5.5.0, 0.12 v5.4.0, 0.10 v5.2.0, 0.00 v5.0.0, 0.14 v4.1.0, 0.00 v4.0.1, 0.20 v4.0.0, 0.29 v3.4.0, 0.25 v3.3.0, 0.33 v3.2.0
% Syntax   : Number of clauses     :   14 (   6 unt;   3 nHn;  12 RR)
%            Number of literals    :   33 (   0 equ;  17 neg)
%            Maximal clause size   :    5 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :   15 (  15 usr;   7 con; 0-3 aty)
%            Number of variables   :   31 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
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

cnf(cls_Zorn_Ochain__extend_0,axiom,
    ( ~ c_in(V_z,V_S,tc_set(T_a))
    | ~ c_in(V_c,c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(c_Zorn_Ochain__extend__1(V_c,V_z,T_a),V_c,tc_set(T_a))
    | c_in(c_union(c_insert(V_z,c_emptyset,tc_set(T_a)),V_c,tc_set(T_a)),c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a))) ) ).

cnf(cls_Zorn_Ochain__extend_1,axiom,
    ( ~ c_in(V_z,V_S,tc_set(T_a))
    | ~ c_in(V_c,c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_lessequals(c_Zorn_Ochain__extend__1(V_c,V_z,T_a),V_z,tc_set(T_a))
    | c_in(c_union(c_insert(V_z,c_emptyset,tc_set(T_a)),V_c,tc_set(T_a)),c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a))) ) ).

cnf(cls_Zorn_Omaxchain__super__lemma_0,axiom,
    ( ~ c_in(V_z,V_x,T_a)
    | ~ c_in(V_c,c_Zorn_Omaxchain(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_in(c_union(c_insert(V_x,c_emptyset,tc_set(T_a)),V_c,tc_set(T_a)),c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(V_z,V_y,T_a)
    | c_in(c_Zorn_Omaxchain__super__lemma__1(V_c,V_y,T_a),V_c,tc_set(T_a)) ) ).

cnf(cls_Zorn_Omaxchain__super__lemma_1,axiom,
    ( ~ c_in(V_z,V_x,T_a)
    | ~ c_in(V_c,c_Zorn_Omaxchain(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_in(c_union(c_insert(V_x,c_emptyset,tc_set(T_a)),V_c,tc_set(T_a)),c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_lessequals(c_Zorn_Omaxchain__super__lemma__1(V_c,V_y,T_a),V_y,tc_set(T_a))
    | c_in(V_z,V_y,T_a) ) ).

cnf(cls_conjecture_0,negated_conjecture,
    c_in(v_c,c_Zorn_Omaxchain(v_S,t_a),tc_set(tc_set(t_a))) ).

cnf(cls_conjecture_1,negated_conjecture,
    c_in(v_c,c_Zorn_Ochain(v_S,t_a),tc_set(tc_set(t_a))) ).

cnf(cls_conjecture_3,negated_conjecture,
    c_in(v_x,v_S,tc_set(t_a)) ).

cnf(cls_conjecture_4,negated_conjecture,
    c_lessequals(v_y,v_x,tc_set(t_a)) ).

cnf(cls_conjecture_5,negated_conjecture,
    c_in(v_xa,v_x,t_a) ).

cnf(cls_conjecture_6,negated_conjecture,
    ~ c_in(v_xa,v_y,t_a) ).

cnf(cls_conjecture_7,negated_conjecture,
    ( c_lessequals(V_U,v_y,tc_set(t_a))
    | ~ c_in(V_U,v_c,tc_set(t_a)) ) ).

%------------------------------------------------------------------------------
