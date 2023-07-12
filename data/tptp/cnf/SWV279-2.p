%------------------------------------------------------------------------------
% File     : SWV279-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Software Verification (Security)
% Problem  : Cryptographic protocol problem for public
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    8 (   2 unt;   0 nHn;   7 RR)
%            Number of literals    :   15 (   0 equ;   8 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :   10 (  10 usr;   5 con; 0-3 aty)
%            Number of variables   :   17 (   3 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_0,negated_conjecture,
    c_in(c_Message_Omsg_OMPair(v_X,v_Y),c_Event_Oused(v_H),tc_Message_Omsg) ).

cnf(cls_conjecture_1,negated_conjecture,
    ( ~ c_in(v_Y,c_Event_Oused(v_H),tc_Message_Omsg)
    | ~ c_in(v_X,c_Event_Oused(v_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__parts_0,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_Y,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_OMPair__parts_1,axiom,
    ( ~ c_in(c_Message_Omsg_OMPair(V_X,V_Y),c_Message_Oparts(V_H),tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Message_Oparts_OInj_0,axiom,
    ( ~ c_in(V_X,V_H,tc_Message_Omsg)
    | c_in(V_X,c_Message_Oparts(V_H),tc_Message_Omsg) ) ).

cnf(cls_Public_Oused__parts__subset__parts_0,axiom,
    ( ~ c_in(V_X,c_Event_Oused(V_evs),tc_Message_Omsg)
    | c_lessequals(c_Message_Oparts(c_insert(V_X,c_emptyset,tc_Message_Omsg)),c_Event_Oused(V_evs),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Set_Oinsert__iff_1,axiom,
    c_in(V_x,c_insert(V_x,V_A,T_a),T_a) ).

cnf(cls_Set_OsubsetD_0,axiom,
    ( ~ c_in(V_c,V_A,T_a)
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | c_in(V_c,V_B,T_a) ) ).

%------------------------------------------------------------------------------
