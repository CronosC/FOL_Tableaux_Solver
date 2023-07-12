%------------------------------------------------------------------------------
% File     : SWV277-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Software Verification (Security)
% Problem  : Cryptographic protocol problem for events
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    5 (   3 unt;   0 nHn;   4 RR)
%            Number of literals    :    8 (   0 equ;   4 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :    8 (   8 usr;   4 con; 0-1 aty)
%            Number of variables   :    7 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Message_Oanalz__subset__parts_0,axiom,
    c_lessequals(c_Message_Oanalz(V_H),c_Message_Oparts(V_H),tc_set(tc_Message_Omsg)) ).

cnf(cls_Message_OkeysFor__mono_0,axiom,
    ( ~ c_lessequals(V_G,V_H,tc_set(tc_Message_Omsg))
    | c_lessequals(c_Message_OkeysFor(V_G),c_Message_OkeysFor(V_H),tc_set(tc_nat)) ) ).

cnf(cls_Set_OsubsetD_0,axiom,
    ( ~ c_in(V_c,V_A,T_a)
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | c_in(V_c,V_B,T_a) ) ).

cnf(cls_conjecture_2,negated_conjecture,
    ~ c_in(v_K,c_Message_OkeysFor(c_Message_Oparts(v_H)),tc_nat) ).

cnf(cls_conjecture_3,negated_conjecture,
    c_in(v_K,c_Message_OkeysFor(c_Message_Oanalz(v_H)),tc_nat) ).

%------------------------------------------------------------------------------
