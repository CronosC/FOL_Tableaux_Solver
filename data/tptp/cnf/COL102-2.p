%------------------------------------------------------------------------------
% File     : COL102-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Combinatory Logic
% Problem  : Problem about combinators
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.06 v5.3.0, 0.10 v5.2.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    6 (   3 unt;   0 nHn;   5 RR)
%            Number of literals    :   10 (   0 equ;   5 neg)
%            Maximal clause size   :    3 (   1 avg)
%            Maximal term depth    :    3 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :   10 (  10 usr;   6 con; 0-4 aty)
%            Number of variables   :   11 (   0 sgn)
% SPC      : CNF_UNS_RFO_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_1,negated_conjecture,
    c_in(c_Pair(v_y,v_za,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_conjecture_2,negated_conjecture,
    c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(v_x,v_z),c_Comb_Ocomb_Oop_A_D_D(v_y,v_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Transitive__Closure_Ortrancl(c_Comb_Ocontract,tc_Comb_Ocomb),tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_conjecture_3,negated_conjecture,
    ~ c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(v_x,v_z),c_Comb_Ocomb_Oop_A_D_D(v_za,v_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Transitive__Closure_Ortrancl(c_Comb_Ocontract,tc_Comb_Ocomb),tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ).

cnf(cls_Comb_Ocontract_OAp1_0,axiom,
    ( ~ c_in(c_Pair(V_x,V_y,tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb))
    | c_in(c_Pair(c_Comb_Ocomb_Oop_A_D_D(V_x,V_z),c_Comb_Ocomb_Oop_A_D_D(V_y,V_z),tc_Comb_Ocomb,tc_Comb_Ocomb),c_Comb_Ocontract,tc_prod(tc_Comb_Ocomb,tc_Comb_Ocomb)) ) ).

cnf(cls_Transitive__Closure_Or__into__rtrancl_0,axiom,
    ( ~ c_in(V_p,V_r,tc_prod(T_a,T_a))
    | c_in(V_p,c_Transitive__Closure_Ortrancl(V_r,T_a),tc_prod(T_a,T_a)) ) ).

cnf(cls_Transitive__Closure_Ortrancl__trans_0,axiom,
    ( ~ c_in(c_Pair(V_b,V_c,T_a,T_a),c_Transitive__Closure_Ortrancl(V_r,T_a),tc_prod(T_a,T_a))
    | ~ c_in(c_Pair(V_a,V_b,T_a,T_a),c_Transitive__Closure_Ortrancl(V_r,T_a),tc_prod(T_a,T_a))
    | c_in(c_Pair(V_a,V_c,T_a,T_a),c_Transitive__Closure_Ortrancl(V_r,T_a),tc_prod(T_a,T_a)) ) ).

%------------------------------------------------------------------------------
