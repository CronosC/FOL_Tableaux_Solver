%------------------------------------------------------------------------------
% File     : LAT272-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Analysis
% Problem  : Problem about Tarski's fixed point theorem
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    4 (   3 unt;   0 nHn;   4 RR)
%            Number of literals    :    6 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-4 aty)
%            Number of functors    :    8 (   8 usr;   6 con; 0-4 aty)
%            Number of variables   :    3 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_4,negated_conjecture,
    c_Tarski_OisLub(v_S,v_cl,v_L,t_a) ).

cnf(cls_conjecture_6,negated_conjecture,
    c_in(v_x,v_S,t_a) ).

cnf(cls_conjecture_7,negated_conjecture,
    ~ c_in(c_Pair(v_x,v_L,t_a,t_a),v_r,tc_prod(t_a,t_a)) ).

cnf(cls_Tarski_O_91_124_AisLub_AS1_Acl_AL1_59_Ay1_A_58_AS1_A_124_93_A_61_61_62_A_Iy1_M_AL1_J_A_58_Ar_A_61_61_ATrue_0,axiom,
    ( ~ c_Tarski_OisLub(V_S,v_cl,V_L,t_a)
    | ~ c_in(V_y,V_S,t_a)
    | c_in(c_Pair(V_y,V_L,t_a,t_a),v_r,tc_prod(t_a,t_a)) ) ).

%------------------------------------------------------------------------------
