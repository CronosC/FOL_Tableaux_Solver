%------------------------------------------------------------------------------
% File     : ANA037-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Analysis
% Problem  : Problem about Big-O notation
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v6.1.0, 0.07 v6.0.0, 0.00 v5.5.0, 0.06 v5.4.0, 0.11 v5.3.0, 0.15 v5.2.0, 0.00 v5.1.0, 0.06 v5.0.0, 0.07 v4.0.1, 0.00 v3.2.0
% Syntax   : Number of clauses     :   10 (   4 unt;   0 nHn;   9 RR)
%            Number of literals    :   20 (   0 equ;  11 neg)
%            Maximal clause size   :    4 (   2 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    5 (   5 usr;   0 prp; 1-3 aty)
%            Number of functors    :   10 (  10 usr;   5 con; 0-3 aty)
%            Number of variables   :   14 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_2,negated_conjecture,
    c_lessequals(c_0,v_f(v_xa),t_b) ).

cnf(cls_conjecture_4,negated_conjecture,
    c_lessequals(c_HOL_Oabs(v_a(v_xa),t_b),c_times(v_c,v_f(v_xa),t_b),t_b) ).

cnf(cls_conjecture_8,negated_conjecture,
    ~ c_lessequals(c_HOL_Oabs(v_a(v_xa),t_b),c_times(c_Orderings_Omax(v_c,v_ca,t_b),v_f(v_xa),t_b),t_b) ).

cnf(tfree_tcs,negated_conjecture,
    class_Ring__and__Field_Oordered__idom(t_b) ).

cnf(cls_Orderings_Ole__maxI1_0,axiom,
    ( ~ class_Orderings_Olinorder(T_b)
    | c_lessequals(V_x,c_Orderings_Omax(V_x,V_y,T_b),T_b) ) ).

cnf(cls_Orderings_Oorder__class_Oorder__trans_0,axiom,
    ( ~ class_Orderings_Oorder(T_a)
    | ~ c_lessequals(V_y,V_z,T_a)
    | ~ c_lessequals(V_x,V_y,T_a)
    | c_lessequals(V_x,V_z,T_a) ) ).

cnf(cls_Ring__and__Field_Opordered__semiring__class_Omult__right__mono_0,axiom,
    ( ~ class_Ring__and__Field_Opordered__semiring(T_a)
    | ~ c_lessequals(V_a,V_b,T_a)
    | ~ c_lessequals(c_0,V_c,T_a)
    | c_lessequals(c_times(V_a,V_c,T_a),c_times(V_b,V_c,T_a),T_a) ) ).

cnf(clsrel_Ring__and__Field_Oordered__idom_33,axiom,
    ( ~ class_Ring__and__Field_Oordered__idom(T)
    | class_Orderings_Olinorder(T) ) ).

cnf(clsrel_Ring__and__Field_Oordered__idom_42,axiom,
    ( ~ class_Ring__and__Field_Oordered__idom(T)
    | class_Ring__and__Field_Opordered__semiring(T) ) ).

cnf(clsrel_Ring__and__Field_Oordered__idom_44,axiom,
    ( ~ class_Ring__and__Field_Oordered__idom(T)
    | class_Orderings_Oorder(T) ) ).

%------------------------------------------------------------------------------