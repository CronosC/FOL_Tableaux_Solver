%------------------------------------------------------------------------------
% File     : SET842-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.00 v4.0.0, 0.14 v3.4.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    7 (   1 unt;   1 nHn;   6 RR)
%            Number of literals    :   14 (   0 equ;   7 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :    7 (   7 usr;   3 con; 0-3 aty)
%            Number of variables   :   17 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_3,negated_conjecture,
    ~ c_lessequals(c_Union(v_Y,tc_set(t_a)),v_m,tc_set(tc_set(t_a))) ).

cnf(cls_conjecture_4,negated_conjecture,
    ( c_lessequals(V_U,v_m,tc_set(tc_set(t_a)))
    | ~ c_in(V_U,v_Y,tc_set(tc_set(t_a))) ) ).

cnf(cls_Set_OUnionE_0,axiom,
    ( ~ c_in(V_A,c_Union(V_C,T_a),T_a)
    | c_in(c_Main_OUnionE__1(V_A,V_C,T_a),V_C,tc_set(T_a)) ) ).

cnf(cls_Set_OUnionE_1,axiom,
    ( ~ c_in(V_A,c_Union(V_C,T_a),T_a)
    | c_in(V_A,c_Main_OUnionE__1(V_A,V_C,T_a),T_a) ) ).

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

%------------------------------------------------------------------------------
