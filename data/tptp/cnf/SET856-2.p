%------------------------------------------------------------------------------
% File     : SET856-2 : TPTP v8.1.2. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.33 v8.1.0, 0.00 v7.3.0, 0.20 v7.2.0, 0.22 v7.1.0, 0.14 v7.0.0, 0.00 v6.2.0, 0.12 v6.0.0, 0.00 v3.3.0, 0.33 v3.2.0
% Syntax   : Number of clauses     :    2 (   2 unt;   0 nHn;   2 RR)
%            Number of literals    :    2 (   0 equ;   1 neg)
%            Maximal clause size   :    1 (   1 avg)
%            Maximal term depth    :    3 (   2 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    7 (   7 usr;   4 con; 0-3 aty)
%            Number of variables   :    0 (   0 sgn)
% SPC      : CNF_UNS_EPR_NEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_3,negated_conjecture,
    c_lessequals(c_Zorn_Osucc(v_S,v_n,t_a),c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) ).

cnf(cls_conjecture_5,negated_conjecture,
    ~ c_lessequals(c_Zorn_Osucc(v_S,v_n,t_a),c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) ).

%------------------------------------------------------------------------------
