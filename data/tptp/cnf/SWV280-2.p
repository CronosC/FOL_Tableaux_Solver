%------------------------------------------------------------------------------
% File     : SWV280-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Software Verification (Security)
% Problem  : Cryptographic protocol problem for public
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    3 (   2 unt;   0 nHn;   1 RR)
%            Number of literals    :    4 (   0 equ;   2 neg)
%            Maximal clause size   :    2 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :    7 (   7 usr;   3 con; 0-3 aty)
%            Number of variables   :    5 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_0,negated_conjecture,
    c_in(c_Message_Omsg_ONonce(V_U),c_Event_Oused(v_evs),tc_Message_Omsg) ).

cnf(cls_Nat_Ole__add1_0,axiom,
    c_lessequals(V_n,c_plus(V_n,V_m,tc_nat),tc_nat) ).

cnf(cls_Public_ONonce__supply__lemma_0,axiom,
    ( ~ c_in(c_Message_Omsg_ONonce(V_U),c_Event_Oused(V_evs),tc_Message_Omsg)
    | ~ c_lessequals(v_sko__urX(V_evs),V_U,tc_nat) ) ).

%------------------------------------------------------------------------------
