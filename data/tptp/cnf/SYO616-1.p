%------------------------------------------------------------------------------
% File     : SYO616-1 : TPTP v8.1.2. Released v7.1.0.
% Domain   : Syntactic
% Problem  : C(2,10)
% Version  : Especial.
% English  :

% Refs     : [Cer15] Cerna (2015), Advances in Schematic Cut Elimination
%          : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer17] Cerna (2017), Email to Geoff Sutcliffe
% Source   : [Cer17]
% Names    : C(2,10) [Cer17]

% Status   : Unsatisfiable
% Rating   : 1.00 v7.3.0, 0.83 v7.1.0
% Syntax   : Number of clauses     :    6 (   1 unt;   1 nHn;   4 RR)
%            Number of literals    :   53 (   0 equ;  48 neg)
%            Maximal clause size   :   23 (   8 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :   32 (   2 sgn)
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
    | eq(f(A),a1) ) ).

cnf(sos_05,axiom,
    ( ~ eq(f(A0),a0)
    | ~ eq(f(A1),a0)
    | ~ eq(f(A2),a0)
    | ~ eq(f(A3),a0)
    | ~ eq(f(A4),a0)
    | ~ eq(f(A5),a0)
    | ~ eq(f(A6),a0)
    | ~ eq(f(A7),a0)
    | ~ eq(f(A8),a0)
    | ~ eq(f(A9),a0)
    | ~ eq(f(A10),a0)
    | ~ eq(f(A11),a0)
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9)
    | ~ le(s(A9),A10)
    | ~ le(s(A10),A11) ) ).

cnf(sos_06,axiom,
    ( ~ eq(f(A0),a1)
    | ~ eq(f(A1),a1)
    | ~ eq(f(A2),a1)
    | ~ eq(f(A3),a1)
    | ~ eq(f(A4),a1)
    | ~ eq(f(A5),a1)
    | ~ eq(f(A6),a1)
    | ~ eq(f(A7),a1)
    | ~ eq(f(A8),a1)
    | ~ eq(f(A9),a1)
    | ~ eq(f(A10),a1)
    | ~ eq(f(A11),a1)
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9)
    | ~ le(s(A9),A10)
    | ~ le(s(A10),A11) ) ).

%------------------------------------------------------------------------------
