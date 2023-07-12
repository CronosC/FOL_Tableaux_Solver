%------------------------------------------------------------------------------
% File     : SWV246-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Software Verification (Security)
% Problem  : Cryptographic protocol problem for messages
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.11 v6.1.0, 0.14 v5.5.0, 0.12 v5.4.0, 0.10 v5.1.0, 0.09 v5.0.0, 0.00 v4.0.0, 0.14 v3.4.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    8 (   2 unt;   2 nHn;   6 RR)
%            Number of literals    :   16 (   0 equ;   7 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    4 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    9 (   9 usr;   5 con; 0-3 aty)
%            Number of variables   :   20 (   3 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_1,negated_conjecture,
    c_in(c_Message_Omsg_OMPair(v_X,v_Y),c_union(c_Message_Oanalz(c_union(v_G,v_H,tc_Message_Omsg)),c_Message_Osynth(v_G),tc_Message_Omsg),tc_Message_Omsg) ).

cnf(cls_conjecture_2,negated_conjecture,
    ~ c_in(v_Y,c_union(c_Message_Oanalz(c_union(v_G,v_H,tc_Message_Omsg)),c_Message_Osynth(v_G),tc_Message_Omsg),tc_Message_Omsg) ).

cnf(cls_Message_OMPair__analz_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oanalz(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__synth_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Osynth(V_H),tc_Message_Omsg)
    | c_in(c_Message_Omsg_OMPair(V_X,V_Y),V_H,tc_Message_Omsg) ) ).

cnf(cls_Message_Oanalz_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Oanalz(V_H),tc_Message_Omsg) ) ).

cnf(cls_Set_OUnCI_0,axiom,
    ( ~ c_in(V_c,V_B,T_a)
    | c_in(V_c,c_union(V_A,V_B,T_a),T_a) ) ).

cnf(cls_Set_OUnCI_1,axiom,
    ( ~ c_in(V_c,V_A,T_a)
    | c_in(V_c,c_union(V_A,V_B,T_a),T_a) ) ).

cnf(cls_Set_OUnE_0,axiom,
    ( ~ c_in(V_c,c_union(V_A,V_B,T_a),T_a)
    | c_in(V_c,V_B,T_a)
    | c_in(V_c,V_A,T_a) ) ).

%------------------------------------------------------------------------------
