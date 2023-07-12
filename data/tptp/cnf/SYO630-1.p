%------------------------------------------------------------------------------
% File     : SYO630-1 : TPTP v8.1.2. Released v7.1.0.
% Domain   : Syntactic
% Problem  : ECSClauseSet5
% Version  : Especial.
% English  :

% Refs     : [Cer15] Cerna (2015), Advances in Schematic Cut Elimination
%          : [CL16]  Cerna & Leitsch (2016), Schematic Cut Elimination and
%          : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer17] Cerna (2017), Email to Geoff Sutcliffe
% Source   : [Cer17]
% Names    : ECSClauseSet5 [Cer17]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.1.0
% Syntax   : Number of clauses     :   32 (  20 unt;   6 nHn;  19 RR)
%            Number of literals    :   60 (   0 equ;  30 neg)
%            Maximal clause size   :    4 (   1 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-1 aty)
%            Number of variables   :   37 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%------------------------------------------------------------------------------
cnf(clause_8_01,axiom,
    ( 'E'(s(s(s(s(s('0'))))),f(A))
    | 'LE'(f(A),s(s(s(s(s('0')))))) ) ).

cnf(clause_13_02,axiom,
    iLEQ(A_2,g(A_2)) ).

cnf(clause_14_03,axiom,
    iLEQ(A_11,g(A_11)) ).

cnf(clause_18_04,axiom,
    iLEQ(A_14,A_14) ).

cnf(clause_31_05,axiom,
    ~ 'E'(f(A_8),f(g(A_8))) ).

cnf(clause_1_06,axiom,
    ( ~ 'LE'(f(A_13),s('0'))
    | ~ iLEQ(A_13,B_8)
    | 'E'('0',f(B_8))
    | 'LE'(f(B_8),'0') ) ).

cnf(clause_6_07,axiom,
    ~ 'LE'(f(A_15),'0') ).

cnf(clause_20_08,axiom,
    iLEQ(A_8,A_8) ).

cnf(clause_19_09,axiom,
    ~ 'E'(f(A_15),f(g(A_15))) ).

cnf(clause_3_10,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_2))
    | ~ 'E'(s(s(s(s(s('0'))))),f(g(A_2)))
    | 'E'(f(A_2),f(g(A_2))) ) ).

cnf(clause_21_11,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_8))
    | ~ 'E'(s(s(s('0'))),f(g(A_8)))
    | 'E'(f(A_8),f(g(A_8))) ) ).

cnf(clause_27_12,axiom,
    ( ~ 'E'(s(s('0')),f(A_11))
    | ~ 'E'(s(s('0')),f(g(A_11)))
    | 'E'(f(A_11),f(g(A_11))) ) ).

cnf(clause_30_13,axiom,
    ( ~ 'E'(s('0'),f(A_14))
    | ~ 'E'(s('0'),f(g(A_14)))
    | 'E'(f(A_14),f(g(A_14))) ) ).

cnf(clause_23_14,axiom,
    ~ 'LE'(f(g(A_15)),'0') ).

cnf(clause_16_15,axiom,
    ( ~ 'LE'(f(A_7),s(s(s('0'))))
    | ~ iLEQ(A_7,B_4)
    | 'E'(s(s('0')),f(B_4))
    | 'LE'(f(B_4),s(s('0'))) ) ).

cnf(clause_7_16,axiom,
    ( ~ 'LE'(f(A_1),s(s(s(s(s('0'))))))
    | ~ iLEQ(A_1,B_0)
    | 'E'(s(s(s(s('0')))),f(B_0))
    | 'LE'(f(B_0),s(s(s(s('0'))))) ) ).

cnf(clause_26_17,axiom,
    ( ~ 'LE'(f(A_4),s(s(s(s('0')))))
    | ~ iLEQ(A_4,B_2)
    | 'E'(s(s(s('0'))),f(B_2))
    | 'LE'(f(B_2),s(s(s('0')))) ) ).

cnf(clause_10_18,axiom,
    iLEQ(A_15,g(A_15)) ).

cnf(clause_4_19,axiom,
    iLEQ(A_5,g(A_5)) ).

cnf(clause_25_20,axiom,
    iLEQ(A_2,A_2) ).

cnf(clause_5_21,axiom,
    ~ 'E'(f(A_5),f(g(A_5))) ).

cnf(clause_0_22,axiom,
    iLEQ(A_14,g(A_14)) ).

cnf(clause_9_23,axiom,
    iLEQ(A_5,A_5) ).

cnf(clause_29_24,axiom,
    ( ~ 'E'('0',f(A_15))
    | ~ 'E'('0',f(g(A_15)))
    | 'E'(f(A_15),f(g(A_15))) ) ).

cnf(clause_22_25,axiom,
    iLEQ(A_8,g(A_8)) ).

cnf(clause_11_26,axiom,
    ~ 'E'(f(A_2),f(g(A_2))) ).

cnf(clause_15_27,axiom,
    iLEQ(A_15,A_15) ).

cnf(clause_28_28,axiom,
    ~ 'E'(f(A_11),f(g(A_11))) ).

cnf(clause_2_29,axiom,
    iLEQ(A_11,A_11) ).

cnf(clause_12_30,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_5))
    | ~ 'E'(s(s(s(s('0')))),f(g(A_5)))
    | 'E'(f(A_5),f(g(A_5))) ) ).

cnf(clause_24_31,axiom,
    ~ 'E'(f(A_14),f(g(A_14))) ).

cnf(clause_17_32,axiom,
    ( ~ 'LE'(f(A_10),s(s('0')))
    | ~ iLEQ(A_10,B_6)
    | 'E'(s('0'),f(B_6))
    | 'LE'(f(B_6),s('0')) ) ).

%------------------------------------------------------------------------------
