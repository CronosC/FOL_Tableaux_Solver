%------------------------------------------------------------------------------
% File     : SET846-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.3.0, 0.05 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    5 (   2 unt;   0 nHn;   4 RR)
%            Number of literals    :    8 (   0 equ;   4 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :    6 (   6 usr;   2 con; 0-3 aty)
%            Number of variables   :   11 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Set_OUnion__upper_0,axiom,
    ( ~ c_in(V_B,V_A,tc_set(T_a))
    | c_lessequals(V_B,c_Union(V_A,T_a),tc_set(T_a)) ) ).

cnf(cls_Set_Osubset__refl_0,axiom,
    c_lessequals(V_A,V_A,tc_set(T_a)) ).

cnf(cls_Zorn_OTFin_OsuccI_0,axiom,
    ( ~ c_in(V_x,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(c_Zorn_Osucc(V_S,V_x,T_a),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a))) ) ).

cnf(cls_Zorn_OTFin__UnionI_0,axiom,
    ( ~ c_lessequals(V_Y,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(tc_set(T_a))))
    | c_in(c_Union(V_Y,tc_set(T_a)),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a))) ) ).

cnf(cls_conjecture_1,negated_conjecture,
    ~ c_lessequals(c_Zorn_Osucc(v_S,c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)),t_a),c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)),tc_set(tc_set(t_a))) ).

%------------------------------------------------------------------------------
