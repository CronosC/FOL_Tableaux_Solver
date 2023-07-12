%------------------------------------------------------------------------------
% File     : SYO617-1 : TPTP v8.1.2. Released v7.1.0.
% Domain   : Syntactic
% Problem  : C(3,0)
% Version  : Especial.
% English  :

% Refs     : [Cer15] Cerna (2015), Advances in Schematic Cut Elimination
%          : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer17] Cerna (2017), Email to Geoff Sutcliffe
% Source   : [Cer17]
% Names    : C(3,0) [Cer17]

% Status   : Unsatisfiable
% Rating   : 0.29 v8.1.0, 0.14 v7.5.0, 0.33 v7.4.0, 0.17 v7.3.0, 0.33 v7.1.0
% Syntax   : Number of clauses     :    7 (   1 unt;   1 nHn;   5 RR)
%            Number of literals    :   17 (   0 equ;  11 neg)
%            Maximal clause size   :    3 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    6 (   6 usr;   3 con; 0-2 aty)
%            Number of variables   :   14 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%------------------------------------------------------------------------------
cnf(sos_01,axiom,
    le(A,A) ).

cnf(sos_02,axiom,
    ( ~ le(max(A,B),C)
    | le(A,C) ) ).

cnf(sos_03,axiom,
    ( ~ le(max(A,B),C)
    | le(B,C) ) ).

cnf(sos_04,axiom,
    ( eq(f(A),a0)
    | eq(f(A),a1)
    | eq(f(A),a2) ) ).

cnf(sos_05,axiom,
    ( ~ eq(f(A0),a0)
    | ~ eq(f(A1),a0)
    | ~ le(s(A0),A1) ) ).

cnf(sos_06,axiom,
    ( ~ eq(f(A0),a1)
    | ~ eq(f(A1),a1)
    | ~ le(s(A0),A1) ) ).

cnf(sos_07,axiom,
    ( ~ eq(f(A0),a2)
    | ~ eq(f(A1),a2)
    | ~ le(s(A0),A1) ) ).

%------------------------------------------------------------------------------
