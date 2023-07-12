%------------------------------------------------------------------------------
% File     : SYO631-1 : TPTP v8.1.2. Released v7.1.0.
% Domain   : Syntactic
% Problem  : ECSClauseSet10
% Version  : Especial.
% English  :

% Refs     : [Cer15] Cerna (2015), Advances in Schematic Cut Elimination
%          : [CL16]  Cerna & Leitsch (2016), Schematic Cut Elimination and
%          : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer17] Cerna (2017), Email to Geoff Sutcliffe
% Source   : [Cer17]
% Names    : ECSClauseSet10 [Cer17]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.4.0, 0.33 v7.1.0
% Syntax   : Number of clauses     :   57 (  35 unt;  11 nHn;  34 RR)
%            Number of literals    :  110 (   0 equ;  55 neg)
%            Maximal clause size   :    4 (   1 avg)
%            Maximal term depth    :   11 (   3 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    4 (   4 usr;   1 con; 0-1 aty)
%            Number of variables   :   67 (   2 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%------------------------------------------------------------------------------
cnf(clause_27_01,axiom,
    ( ~ 'E'(s(s(s(s(s(s(s(s(s('0'))))))))),f(A_5))
    | ~ 'E'(s(s(s(s(s(s(s(s(s('0'))))))))),f(g(A_5)))
    | 'E'(f(A_5),f(g(A_5))) ) ).

cnf(clause_3_02,axiom,
    iLEQ(A_23,g(A_23)) ).

cnf(clause_8_03,axiom,
    ( ~ 'LE'(f(A_19),s(s(s(s('0')))))
    | ~ iLEQ(A_19,B_12)
    | 'E'(s(s(s('0'))),f(B_12))
    | 'LE'(f(B_12),s(s(s('0')))) ) ).

cnf(clause_48_04,axiom,
    ( ~ 'LE'(f(A_1),s(s(s(s(s(s(s(s(s(s('0')))))))))))
    | ~ iLEQ(A_1,B_0)
    | 'E'(s(s(s(s(s(s(s(s(s('0'))))))))),f(B_0))
    | 'LE'(f(B_0),s(s(s(s(s(s(s(s(s('0')))))))))) ) ).

cnf(clause_19_05,axiom,
    ~ 'E'(f(A_26),f(g(A_26))) ).

cnf(clause_18_06,axiom,
    iLEQ(A_14,A_14) ).

cnf(clause_44_07,axiom,
    ( ~ 'E'(s(s(s(s(s(s(s('0'))))))),f(A_11))
    | ~ 'E'(s(s(s(s(s(s(s('0'))))))),f(g(A_11)))
    | 'E'(f(A_11),f(g(A_11))) ) ).

cnf(clause_21_08,axiom,
    iLEQ(A_8,A_8) ).

cnf(clause_41_09,axiom,
    ~ 'E'(f(A_30),f(g(A_30))) ).

cnf(clause_28_10,axiom,
    iLEQ(A_8,g(A_8)) ).

cnf(clause_5_11,axiom,
    ( ~ 'LE'(f(A_13),s(s(s(s(s(s('0')))))))
    | ~ iLEQ(A_13,B_8)
    | 'E'(s(s(s(s(s('0'))))),f(B_8))
    | 'LE'(f(B_8),s(s(s(s(s('0')))))) ) ).

cnf(clause_29_12,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_23))
    | ~ 'E'(s(s(s('0'))),f(g(A_23)))
    | 'E'(f(A_23),f(g(A_23))) ) ).

cnf(clause_10_13,axiom,
    ( ~ 'LE'(f(A_4),s(s(s(s(s(s(s(s(s('0'))))))))))
    | ~ iLEQ(A_4,B_2)
    | 'E'(s(s(s(s(s(s(s(s('0')))))))),f(B_2))
    | 'LE'(f(B_2),s(s(s(s(s(s(s(s('0'))))))))) ) ).

cnf(clause_9_14,axiom,
    ~ 'E'(f(A_29),f(g(A_29))) ).

cnf(clause_32_15,axiom,
    iLEQ(A_20,g(A_20)) ).

cnf(clause_11_16,axiom,
    ( ~ 'E'(s(s(s(s(s(s('0')))))),f(A_14))
    | ~ 'E'(s(s(s(s(s(s('0')))))),f(g(A_14)))
    | 'E'(f(A_14),f(g(A_14))) ) ).

cnf(clause_1_17,axiom,
    iLEQ(A_14,g(A_14)) ).

cnf(clause_16_18,axiom,
    iLEQ(A_2,g(A_2)) ).

cnf(clause_26_19,axiom,
    ( ~ 'LE'(f(A_7),s(s(s(s(s(s(s(s('0')))))))))
    | ~ iLEQ(A_7,B_4)
    | 'E'(s(s(s(s(s(s(s('0'))))))),f(B_4))
    | 'LE'(f(B_4),s(s(s(s(s(s(s('0')))))))) ) ).

cnf(clause_35_20,axiom,
    iLEQ(A_26,A_26) ).

cnf(clause_23_21,axiom,
    ( ~ 'LE'(f(A_25),s(s('0')))
    | ~ iLEQ(A_25,B_16)
    | 'E'(s('0'),f(B_16))
    | 'LE'(f(B_16),s('0')) ) ).

cnf(clause_20_22,axiom,
    ( ~ 'E'(s(s('0')),f(A_26))
    | ~ 'E'(s(s('0')),f(g(A_26)))
    | 'E'(f(A_26),f(g(A_26))) ) ).

cnf(clause_40_23,axiom,
    ( ~ 'E'(s(s(s(s(s('0'))))),f(A_17))
    | ~ 'E'(s(s(s(s(s('0'))))),f(g(A_17)))
    | 'E'(f(A_17),f(g(A_17))) ) ).

cnf(clause_53_24,axiom,
    ~ 'E'(f(A_8),f(g(A_8))) ).

cnf(clause_2_25,axiom,
    ( ~ 'E'('0',f(A_30))
    | ~ 'E'('0',f(g(A_30)))
    | 'E'(f(A_30),f(g(A_30))) ) ).

cnf(clause_50_26,axiom,
    iLEQ(A_30,A_30) ).

cnf(clause_37_27,axiom,
    iLEQ(A_23,A_23) ).

cnf(clause_14_28,axiom,
    ~ 'E'(f(A_23),f(g(A_23))) ).

cnf(clause_45_29,axiom,
    iLEQ(A_26,g(A_26)) ).

cnf(clause_43_30,axiom,
    ~ 'E'(f(A_11),f(g(A_11))) ).

cnf(clause_56_31,axiom,
    ( ~ 'LE'(f(A_28),s('0'))
    | ~ iLEQ(A_28,B_18)
    | 'E'('0',f(B_18))
    | 'LE'(f(B_18),'0') ) ).

cnf(clause_42_32,axiom,
    ( ~ 'E'(s(s(s(s(s(s(s(s(s(s('0')))))))))),f(A_2))
    | ~ 'E'(s(s(s(s(s(s(s(s(s(s('0')))))))))),f(g(A_2)))
    | 'E'(f(A_2),f(g(A_2))) ) ).

cnf(clause_13_33,axiom,
    iLEQ(A_5,A_5) ).

cnf(clause_12_34,axiom,
    iLEQ(A_20,A_20) ).

cnf(clause_30_35,axiom,
    ( ~ 'E'(s('0'),f(A_29))
    | ~ 'E'(s('0'),f(g(A_29)))
    | 'E'(f(A_29),f(g(A_29))) ) ).

cnf(clause_0_36,axiom,
    ( ~ 'LE'(f(A_16),s(s(s(s(s('0'))))))
    | ~ iLEQ(A_16,B_10)
    | 'E'(s(s(s(s('0')))),f(B_10))
    | 'LE'(f(B_10),s(s(s(s('0'))))) ) ).

cnf(clause_33_37,axiom,
    ~ 'E'(f(A_20),f(g(A_20))) ).

cnf(clause_6_38,axiom,
    iLEQ(A_5,g(A_5)) ).

cnf(clause_49_39,axiom,
    ( 'E'(s(s(s(s(s(s(s(s(s(s('0')))))))))),f(A))
    | 'LE'(f(A),s(s(s(s(s(s(s(s(s(s('0'))))))))))) ) ).

cnf(clause_52_40,axiom,
    iLEQ(A_17,A_17) ).

cnf(clause_4_41,axiom,
    iLEQ(A_11,A_11) ).

cnf(clause_25_42,axiom,
    ~ 'E'(f(A_17),f(g(A_17))) ).

cnf(clause_46_43,axiom,
    iLEQ(A_30,g(A_30)) ).

cnf(clause_17_44,axiom,
    iLEQ(A_11,g(A_11)) ).

cnf(clause_54_45,axiom,
    ( ~ 'LE'(f(A_10),s(s(s(s(s(s(s('0'))))))))
    | ~ iLEQ(A_10,B_6)
    | 'E'(s(s(s(s(s(s('0')))))),f(B_6))
    | 'LE'(f(B_6),s(s(s(s(s(s('0'))))))) ) ).

cnf(clause_39_46,axiom,
    iLEQ(A_2,A_2) ).

cnf(clause_47_47,axiom,
    iLEQ(A_17,g(A_17)) ).

cnf(clause_55_48,axiom,
    ( ~ 'E'(s(s(s(s('0')))),f(A_20))
    | ~ 'E'(s(s(s(s('0')))),f(g(A_20)))
    | 'E'(f(A_20),f(g(A_20))) ) ).

cnf(clause_15_49,axiom,
    ~ 'E'(f(A_2),f(g(A_2))) ).

cnf(clause_51_50,axiom,
    ( ~ 'LE'(f(A_22),s(s(s('0'))))
    | ~ iLEQ(A_22,B_14)
    | 'E'(s(s('0')),f(B_14))
    | 'LE'(f(B_14),s(s('0'))) ) ).

cnf(clause_36_51,axiom,
    ~ 'LE'(f(g(A_30)),'0') ).

cnf(clause_38_52,axiom,
    ~ 'LE'(f(A_30),'0') ).

cnf(clause_7_53,axiom,
    ~ 'E'(f(A_5),f(g(A_5))) ).

cnf(clause_31_54,axiom,
    ( ~ 'E'(s(s(s(s(s(s(s(s('0')))))))),f(A_8))
    | ~ 'E'(s(s(s(s(s(s(s(s('0')))))))),f(g(A_8)))
    | 'E'(f(A_8),f(g(A_8))) ) ).

cnf(clause_34_55,axiom,
    ~ 'E'(f(A_14),f(g(A_14))) ).

cnf(clause_22_56,axiom,
    iLEQ(A_29,g(A_29)) ).

cnf(clause_24_57,axiom,
    iLEQ(A_29,A_29) ).

%------------------------------------------------------------------------------
