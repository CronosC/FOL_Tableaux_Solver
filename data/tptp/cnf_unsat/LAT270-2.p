%------------------------------------------------------------------------------
% File     : LAT270-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Analysis
% Problem  : Problem about Tarski's fixed point theorem
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    5 (   4 unt;   0 nHn;   5 RR)
%            Number of literals    :    8 (   0 equ;   4 neg)
%            Maximal clause size   :    4 (   1 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 3-3 aty)
%            Number of functors    :    8 (   8 usr;   6 con; 0-4 aty)
%            Number of variables   :    3 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_0,negated_conjecture,
    c_in(v_a,v_A,t_a) ).

cnf(cls_conjecture_1,negated_conjecture,
    c_in(v_b,v_A,t_a) ).

cnf(cls_conjecture_2,negated_conjecture,
    c_lessequals(v_S,c_Tarski_Ointerval(v_r,v_a,v_b,t_a),tc_set(t_a)) ).

cnf(cls_conjecture_6,negated_conjecture,
    ~ c_lessequals(v_S,v_A,tc_set(t_a)) ).

cnf(cls_Tarski_O_91_124_Aa1_A_58_AA_59_Ab1_A_58_AA_59_AS1_A_60_61_Ainterval_Ar_Aa1_Ab1_A_124_93_A_61_61_62_AS1_A_60_61_AA_A_61_61_ATrue_0,axiom,
    ( ~ c_in(V_b,v_A,t_a)
    | ~ c_in(V_a,v_A,t_a)
    | ~ c_lessequals(V_S,c_Tarski_Ointerval(v_r,V_a,V_b,t_a),tc_set(t_a))
    | c_lessequals(V_S,v_A,tc_set(t_a)) ) ).

%------------------------------------------------------------------------------
