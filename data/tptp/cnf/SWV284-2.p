%------------------------------------------------------------------------------
% File     : SWV284-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Software Verification (Security)
% Problem  : Cryptographic protocol problem for shared
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v7.5.0, 0.17 v7.4.0, 0.00 v7.1.0, 0.17 v7.0.0, 0.12 v6.3.0, 0.14 v6.2.0, 0.11 v6.1.0, 0.14 v5.5.0, 0.12 v5.4.0, 0.10 v5.1.0, 0.09 v5.0.0, 0.00 v4.0.0, 0.14 v3.4.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    6 (   1 unt;   1 nHn;   4 RR)
%            Number of literals    :   11 (   0 equ;   6 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :   13 (  13 usr;   6 con; 0-3 aty)
%            Number of variables   :   11 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_0,negated_conjecture,
    c_lessequals(V_U,v_x(V_U),tc_nat) ).

cnf(cls_conjecture_1,negated_conjecture,
    ( ~ c_in(c_Message_Omsg_ONonce(V_U),c_Event_Oused(v_list),tc_Message_Omsg)
    | ~ c_lessequals(v_N,V_U,tc_nat) ) ).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_in(c_Message_Omsg_ONonce(v_x(V_U)),c_Event_Oused(v_list),tc_Message_Omsg)
    | c_in(c_Message_Omsg_ONonce(v_x(V_U)),c_Message_Oparts(c_insert(v_msg,c_emptyset,tc_Message_Omsg)),tc_Message_Omsg) ) ).

cnf(cls_Message_Omsg__Nonce__supply_0,axiom,
    ( ~ c_in(c_Message_Omsg_ONonce(V_U),c_Message_Oparts(c_insert(V_msg,c_emptyset,tc_Message_Omsg)),tc_Message_Omsg)
    | ~ c_lessequals(v_sko__upX(V_msg),V_U,tc_nat) ) ).

cnf(cls_Nat_Oadd__leE_0,axiom,
    ( ~ c_lessequals(c_plus(V_m,V_k,tc_nat),V_n,tc_nat)
    | c_lessequals(V_k,V_n,tc_nat) ) ).

cnf(cls_Nat_Oadd__leE_1,axiom,
    ( ~ c_lessequals(c_plus(V_m,V_k,tc_nat),V_n,tc_nat)
    | c_lessequals(V_m,V_n,tc_nat) ) ).

%------------------------------------------------------------------------------
