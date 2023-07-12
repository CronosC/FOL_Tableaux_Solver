%------------------------------------------------------------------------------
% File     : ANA042-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Analysis
% Problem  : Problem about Big-O notation
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.05 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    2 (   2 unt;   0 nHn;   1 RR)
%            Number of literals    :    2 (   0 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    4 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    8 (   8 usr;   2 con; 0-3 aty)
%            Number of variables   :    3 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_1,negated_conjecture,
    c_lessequals(c_HOL_Oabs(v_f(V_U,V_V),t_c),c_times(v_x,v_h(V_U,V_V),t_c),t_c) ).

cnf(cls_conjecture_3,negated_conjecture,
    ~ c_lessequals(c_HOL_Oabs(v_f(v_xa(V_U),v_xb(V_U)),t_c),c_times(V_U,v_h(v_xa(V_U),v_xb(V_U)),t_c),t_c) ).

%------------------------------------------------------------------------------
