%------------------------------------------------------------------------------
% File     : SWV259-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Software Verification (Security)
% Problem  : Cryptographic protocol problem for messages
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    5 (   2 unt;   0 nHn;   4 RR)
%            Number of literals    :    8 (   0 equ;   4 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    6 (   6 usr;   3 con; 0-3 aty)
%            Number of variables   :   10 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_1,negated_conjecture,
    ~ c_lessequals(c_Message_Oparts(v_H),c_Message_Oparts(c_insert(v_X,v_H,tc_Message_Omsg)),tc_set(tc_Message_Omsg)) ).

cnf(cls_Message_Oparts__subset__iff_0,axiom,
    ( ~ c_lessequals(c_Message_Oparts(V_G),c_Message_Oparts(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(V_G,c_Message_Oparts(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Message_Oparts__subset__iff_1,axiom,
    ( ~ c_lessequals(V_G,c_Message_Oparts(V_H),tc_set(tc_Message_Omsg))
    | c_lessequals(c_Message_Oparts(V_G),c_Message_Oparts(V_H),tc_set(tc_Message_Omsg)) ) ).

cnf(cls_Set_Oinsert__subset_1,axiom,
    ( ~ c_lessequals(c_insert(V_x,V_A,T_a),V_B,tc_set(T_a))
    | c_lessequals(V_A,V_B,tc_set(T_a)) ) ).

cnf(cls_Set_Osubset__refl_0,axiom,
    c_lessequals(V_A,V_A,tc_set(T_a)) ).

%------------------------------------------------------------------------------
