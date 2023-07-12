%------------------------------------------------------------------------------
% File     : SWV242-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Software Verification (Security)
% Problem  : Cryptographic protocol problem for messages
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.3.0, 0.05 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    7 (   4 unt;   0 nHn;   5 RR)
%            Number of literals    :   11 (   0 equ;   5 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    8 (   8 usr;   5 con; 0-3 aty)
%            Number of variables   :   12 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_0,negated_conjecture,
    c_lessequals(v_G,c_Message_Oanalz(v_G_H),tc_set(tc_Message_Omsg)) ).

cnf(cls_conjecture_1,negated_conjecture,
    c_lessequals(v_H,c_Message_Oanalz(v_H_H),tc_set(tc_Message_Omsg)) ).

cnf(cls_conjecture_2,negated_conjecture,
    ( ~ c_lessequals(v_H,c_Message_Oanalz(c_union(v_G_H,v_H_H,tc_Message_Omsg)),tc_set(tc_Message_Omsg))
    | ~ c_lessequals(v_G,c_Message_Oanalz(c_union(v_G_H,v_H_H,tc_Message_Omsg)),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Oanalz__mono_0,axiom,
    ( ~ c_lessequals(V_G,V_H,tc_set(tc_Message_Omsg))
    | c_lessequals(c_Message_Oanalz(V_G),c_Message_Oanalz(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Set_OUn__upper1_0,axiom,
    c_lessequals(V_A,c_union(V_A,V_B,T_a),tc_set(T_a)) ).

cnf(cls_Set_OUn__upper2_0,axiom,
    c_lessequals(V_B,c_union(V_A,V_B,T_a),tc_set(T_a)) ).

cnf(cls_Set_Osubset__trans_0,axiom,
    ( ~ c_lessequals(V_B,V_C,tc_set(T_a))
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | c_lessequals(V_A,V_C,tc_set(T_a)) ) ).

%------------------------------------------------------------------------------
