%------------------------------------------------------------------------------
% File     : LAT271-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Analysis
% Problem  : Problem about Tarski's fixed point theorem
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v8.1.0, 0.25 v7.4.0, 0.17 v7.3.0, 0.25 v6.2.0, 0.17 v6.1.0, 0.00 v5.4.0, 0.06 v5.3.0, 0.05 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    4 (   3 unt;   0 nHn;   4 RR)
%            Number of literals    :    6 (   0 equ;   3 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :   10 (  10 usr;   6 con; 0-4 aty)
%            Number of variables   :    6 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_2,negated_conjecture,
    c_lessequals(v_S,c_Tarski_Ointerval(v_r,v_a,v_b,t_a),tc_set(t_a)) ).

cnf(cls_conjecture_6,negated_conjecture,
    c_in(v_x,v_S,t_a) ).

cnf(cls_conjecture_7,negated_conjecture,
    ~ c_in(c_Pair(v_a,v_x,t_a,t_a),v_r,tc_prod(t_a,t_a)) ).

cnf(cls_Tarski_O_91_124_AS1_A_60_61_Ainterval_Ar_Aa1_Ab1_59_Ax1_A_58_AS1_A_124_93_A_61_61_62_A_Ia1_M_Ax1_J_A_58_Ar_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_x,V_S,T_a)
    | ~ c_lessequals(V_S,c_Tarski_Ointerval(V_r,V_a,V_b,T_a),tc_set(T_a))
    | c_in(c_Pair(V_a,V_x,T_a,T_a),V_r,tc_prod(T_a,T_a)) ) ).

%------------------------------------------------------------------------------
