%------------------------------------------------------------------------------
% File     : SYO626-1 : TPTP v8.1.2. Released v7.1.0.
% Domain   : Syntactic
% Problem  : C(8,8)
% Version  : Especial.
% English  :

% Refs     : [Cer15] Cerna (2015), Advances in Schematic Cut Elimination
%          : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer17] Cerna (2017), Email to Geoff Sutcliffe
% Source   : [Cer17]
% Names    : C(8,8) [Cer17]

% Status   : Unsatisfiable
% Rating   : 1.00 v7.1.0
% Syntax   : Number of clauses     :   12 (   1 unt;   1 nHn;  10 RR)
%            Number of literals    :  165 (   0 equ; 154 neg)
%            Maximal clause size   :   19 (  13 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   2 usr;   0 prp; 2-2 aty)
%            Number of functors    :   11 (  11 usr;   8 con; 0-2 aty)
%            Number of variables   :   88 (   2 sgn)
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
    | eq(f(A),a2)
    | eq(f(A),a3)
    | eq(f(A),a4)
    | eq(f(A),a5)
    | eq(f(A),a6)
    | eq(f(A),a7) ) ).

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
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9) ) ).

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
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9) ) ).

cnf(sos_07,axiom,
    ( ~ eq(f(A0),a2)
    | ~ eq(f(A1),a2)
    | ~ eq(f(A2),a2)
    | ~ eq(f(A3),a2)
    | ~ eq(f(A4),a2)
    | ~ eq(f(A5),a2)
    | ~ eq(f(A6),a2)
    | ~ eq(f(A7),a2)
    | ~ eq(f(A8),a2)
    | ~ eq(f(A9),a2)
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9) ) ).

cnf(sos_08,axiom,
    ( ~ eq(f(A0),a3)
    | ~ eq(f(A1),a3)
    | ~ eq(f(A2),a3)
    | ~ eq(f(A3),a3)
    | ~ eq(f(A4),a3)
    | ~ eq(f(A5),a3)
    | ~ eq(f(A6),a3)
    | ~ eq(f(A7),a3)
    | ~ eq(f(A8),a3)
    | ~ eq(f(A9),a3)
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9) ) ).

cnf(sos_09,axiom,
    ( ~ eq(f(A0),a4)
    | ~ eq(f(A1),a4)
    | ~ eq(f(A2),a4)
    | ~ eq(f(A3),a4)
    | ~ eq(f(A4),a4)
    | ~ eq(f(A5),a4)
    | ~ eq(f(A6),a4)
    | ~ eq(f(A7),a4)
    | ~ eq(f(A8),a4)
    | ~ eq(f(A9),a4)
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9) ) ).

cnf(sos_10,axiom,
    ( ~ eq(f(A0),a5)
    | ~ eq(f(A1),a5)
    | ~ eq(f(A2),a5)
    | ~ eq(f(A3),a5)
    | ~ eq(f(A4),a5)
    | ~ eq(f(A5),a5)
    | ~ eq(f(A6),a5)
    | ~ eq(f(A7),a5)
    | ~ eq(f(A8),a5)
    | ~ eq(f(A9),a5)
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9) ) ).

cnf(sos_11,axiom,
    ( ~ eq(f(A0),a6)
    | ~ eq(f(A1),a6)
    | ~ eq(f(A2),a6)
    | ~ eq(f(A3),a6)
    | ~ eq(f(A4),a6)
    | ~ eq(f(A5),a6)
    | ~ eq(f(A6),a6)
    | ~ eq(f(A7),a6)
    | ~ eq(f(A8),a6)
    | ~ eq(f(A9),a6)
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9) ) ).

cnf(sos_12,axiom,
    ( ~ eq(f(A0),a7)
    | ~ eq(f(A1),a7)
    | ~ eq(f(A2),a7)
    | ~ eq(f(A3),a7)
    | ~ eq(f(A4),a7)
    | ~ eq(f(A5),a7)
    | ~ eq(f(A6),a7)
    | ~ eq(f(A7),a7)
    | ~ eq(f(A8),a7)
    | ~ eq(f(A9),a7)
    | ~ le(s(A0),A1)
    | ~ le(s(A1),A2)
    | ~ le(s(A2),A3)
    | ~ le(s(A3),A4)
    | ~ le(s(A4),A5)
    | ~ le(s(A5),A6)
    | ~ le(s(A6),A7)
    | ~ le(s(A7),A8)
    | ~ le(s(A8),A9) ) ).

%------------------------------------------------------------------------------
