%------------------------------------------------------------------------------
% File     : SYO679-1 : TPTP v8.1.2. Released v7.3.0.
% Domain   : Syntactic
% Problem  : GSM_4_1_4
% Version  : Especial.
% English  :

% Refs     : [EH+16] Ebner et al. (2016), System Description: GAPT 2.0
%          : [Cer18] Cerna (2018), Email to Geoff Sutcliffe
% Source   : [Cer18]
% Names    : GSM_4_1_4 [Cer18]

% Status   : Unsatisfiable
% Rating   : 0.14 v8.1.0, 0.00 v7.5.0, 0.17 v7.4.0, 0.33 v7.3.0
% Syntax   : Number of clauses     :  102 (   2 unt;  68 nHn; 101 RR)
%            Number of literals    :  970 (   0 equ; 805 neg)
%            Maximal clause size   :   17 (   9 avg)
%            Maximal term depth    :    6 (   2 avg)
%            Number of predicates  :    3 (   3 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-1 aty)
%            Number of variables   :  165 (   1 sgn)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : Created using the GAPT system - https://github.com/gapt/gapt/blob/
%            master/examples/schema/GradedStrictMonotoneSequenceSchema.scala
%------------------------------------------------------------------------------
cnf(clause_325,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_10),f(suc(suc(B_10)))) ) ).

cnf(clause_1076,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_10),f(suc(suc(B_10)))) ) ).

cnf(clause_17,axiom,
    ( ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_725,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_13))))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(suc(B_13))))))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_1657,axiom,
    ( ~ 'LE'(f(B_16),s('0'))
    | 'E'('0',f(B_16))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_1300,axiom,
    ( ~ 'E'(f(B_14),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_14))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(suc(A_3))))) ) ).

cnf(clause_812,axiom,
    ( ~ 'LE'(f(B_9),s(s(s('0'))))
    | 'E'(s(s('0')),f(B_9))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_957,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_969,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(B_10),f(suc(suc(suc(B_10))))) ) ).

cnf(clause_141,axiom,
    ( ~ 'LE'(f(B_13),s(s('0')))
    | 'E'(s('0'),f(B_13))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_1237,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_14),f(suc(suc(suc(B_14))))) ) ).

cnf(clause_257,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_973,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_5),f(suc(suc(B_5)))) ) ).

cnf(clause_1274,axiom,
    ( ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_1))))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1386,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_9)))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(B_9)))))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_1310,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_152,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_14),f(suc(suc(B_14)))) ) ).

cnf(clause_624,axiom,
    ( ~ 'LE'(f(B_4),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(B_4))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_1280,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_14),f(suc(suc(suc(B_14))))) ) ).

cnf(clause_154,axiom,
    ( ~ 'LE'(f(suc(suc(B_9))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(B_9))))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_1318,axiom,
    'LE'(f(A),s(s(s(s('0'))))) ).

cnf(clause_883,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_10))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10)))) ) ).

cnf(clause_322,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_14),f(suc(suc(suc(B_14))))) ) ).

cnf(clause_1353,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_10),f(suc(suc(suc(B_10))))) ) ).

cnf(clause_618,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_5))))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(B_5),f(suc(suc(B_5))))
    | 'E'(f(A_1),f(suc(A_1))) ) ).

cnf(clause_476,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_16)))),s('0'))
    | 'E'('0',f(suc(suc(suc(B_16)))))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_463,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_933,axiom,
    ( ~ 'LE'(f(suc(B_9)),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(B_9)))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_663,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(B_17))))))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'(f(B_17),f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4)))) ) ).

cnf(clause_1330,axiom,
    ( ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | 'E'(f(A_3),f(suc(A_3)))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_755,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_10))))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(suc(A_2)))) ) ).

cnf(clause_685,axiom,
    ( ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1664,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_10),f(suc(suc(B_10)))) ) ).

cnf(clause_1373,axiom,
    ( ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_372,axiom,
    ( ~ 'E'(f(B_14),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_14))))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(A_3))) ) ).

cnf(clause_1562,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_1022,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(B_14),f(suc(suc(B_14)))) ) ).

cnf(clause_1773,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(B_5),f(suc(suc(B_5))))
    | 'E'(f(B_5),f(suc(suc(suc(B_5))))) ) ).

cnf(clause_1725,axiom,
    ( ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_67,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | 'E'(f(B_14),f(suc(suc(B_14)))) ) ).

cnf(clause_508,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_900,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(B_17))))))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'(f(B_17),f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(A_4))))) ) ).

cnf(clause_35,axiom,
    ( ~ 'LE'(f(suc(B_16)),s('0'))
    | 'E'('0',f(suc(B_16)))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_920,axiom,
    ( ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(A_2)))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_734,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_4))))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_815,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | 'E'(f(B_17),f(suc(suc(suc(B_17))))) ) ).

cnf(clause_350,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_4))))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_4))))))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_1217,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_69,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_1037,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_9))))),s(s(s('0'))))
    | 'E'(s(s('0')),f(suc(suc(suc(suc(B_9))))))
    | 'LE'(f(B_9),s(s('0'))) ) ).

cnf(clause_1588,axiom,
    ( ~ 'E'(f(B_14),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_14))))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(A_3)))) ) ).

cnf(clause_1392,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | 'E'(f(B_10),f(suc(suc(suc(B_10))))) ) ).

cnf(clause_356,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_751,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(A_4))))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_1529,axiom,
    ( ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_30,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_5),f(suc(suc(B_5)))) ) ).

cnf(clause_781,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | 'E'(f(B_17),f(suc(suc(suc(B_17))))) ) ).

cnf(clause_319,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | 'E'(f(B_17),f(suc(B_17))) ) ).

cnf(clause_531,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | iLEQ(suc(A_1),suc(A_1)) ) ).

cnf(clause_768,axiom,
    ( ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(A_2))
    | 'E'(f(A_2),f(suc(suc(A_2))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_942,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_4))))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_158,axiom,
    ( ~ 'E'(f(B_14),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(B_14))))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14)) ) ).

cnf(clause_309,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(B_5),f(suc(suc(B_5))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_5),f(suc(suc(suc(B_5))))) ) ).

cnf(clause_1277,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_4))))))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(B_17),f(suc(suc(suc(B_17))))) ) ).

cnf(clause_363,axiom,
    ( ~ 'LE'(f(suc(B_13)),s(s('0')))
    | 'E'(s('0'),f(suc(B_13)))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_782,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_5))))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(B_5),f(suc(suc(B_5))))
    | 'E'(f(A_1),f(suc(suc(suc(A_1))))) ) ).

cnf(clause_440,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_4))))))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_1713,axiom,
    ( ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_10))))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(f(B_10),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(A_2))) ) ).

cnf(clause_1648,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_5),f(suc(suc(B_5)))) ) ).

cnf(clause_876,axiom,
    ~ 'LE'(f(z),'0') ).

cnf(clause_533,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_1))))))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_1620,axiom,
    ( ~ 'LE'(f(suc(suc(B_4))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(B_4))))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_830,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | 'E'(f(B_17),f(suc(suc(B_17)))) ) ).

cnf(clause_8,axiom,
    ( ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_129,axiom,
    ( ~ 'LE'(f(suc(B_4)),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(B_4)))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_1594,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(B_5),f(suc(suc(B_5))))
    | 'E'(f(A_1),f(suc(A_1)))
    | 'E'(f(B_5),f(suc(suc(suc(B_5))))) ) ).

cnf(clause_642,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(A_2))))))
    | ~ 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(B_10),f(suc(suc(B_10)))) ) ).

cnf(clause_410,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(B_14)))))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(f(B_14),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(B_14),f(suc(suc(suc(B_14))))) ) ).

cnf(clause_1604,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_13)))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(suc(B_13)))))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_1079,axiom,
    ( ~ 'LE'(f(suc(suc(suc(suc(B_16))))),s('0'))
    | 'E'('0',f(suc(suc(suc(suc(B_16))))))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_1006,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(f(A_3),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(suc(suc(suc(suc(A_3))))))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(f(A_3),f(suc(suc(suc(A_3)))))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_625,axiom,
    ( ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | iLEQ(suc(A_3),suc(A_3)) ) ).

cnf(clause_1728,axiom,
    ( ~ 'E'('0',f(A_4))
    | ~ 'E'('0',f(suc(A_4)))
    | 'E'(f(A_4),f(suc(A_4)))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_952,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | iLEQ(suc(A_2),suc(A_2)) ) ).

cnf(clause_1356,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_5))))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(A_1))))))
    | ~ 'E'(f(B_5),f(suc(suc(B_5)))) ) ).

cnf(clause_157,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(B_17))))))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'(f(B_17),f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4))) ) ).

cnf(clause_1430,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(A_1)))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(suc(A_1)))))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_484,axiom,
    ( ~ 'LE'(f(suc(suc(B_13))),s(s('0')))
    | 'E'(s('0'),f(suc(suc(B_13))))
    | 'LE'(f(B_13),s('0')) ) ).

cnf(clause_1357,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_10),f(suc(suc(suc(B_10))))) ) ).

cnf(clause_1674,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_5),f(suc(B_5))) ) ).

cnf(clause_225,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(f(B_10),f(suc(suc(B_10))))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(B_10)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(suc(B_10))))))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | ~ 'E'(f(B_10),f(suc(suc(suc(B_10)))))
    | ~ 'E'(s(s('0')),f(suc(suc(B_10))))
    | 'E'(f(A_2),f(suc(suc(suc(A_2))))) ) ).

cnf(clause_845,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(A_3),f(suc(A_3)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ 'E'(s('0'),f(suc(suc(A_3))))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(suc(A_3))))
    | 'E'(f(B_14),f(suc(B_14))) ) ).

cnf(clause_47,axiom,
    ( ~ 'LE'(f(suc(suc(suc(B_4)))),s(s(s(s('0')))))
    | 'E'(s(s(s('0'))),f(suc(suc(suc(B_4)))))
    | 'LE'(f(B_4),s(s(s('0')))) ) ).

cnf(clause_72,axiom,
    ( ~ 'E'('0',f(suc(suc(suc(suc(B_17))))))
    | ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'('0',f(suc(suc(suc(suc(A_4))))))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'(f(B_17),f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4)) ) ).

cnf(clause_112,axiom,
    ( ~ 'E'(f(A_4),f(suc(A_4)))
    | ~ 'E'('0',f(suc(suc(suc(A_4)))))
    | ~ 'E'('0',f(suc(suc(A_4))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(A_4),f(suc(suc(A_4))))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(suc(suc(A_4)))))
    | iLEQ(suc(A_4),suc(A_4)) ) ).

cnf(clause_578,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(suc(B_5))))))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(B_5),f(suc(suc(B_5))))
    | 'E'(f(A_1),f(suc(suc(A_1)))) ) ).

cnf(clause_500,axiom,
    ( ~ 'E'('0',f(suc(B_17)))
    | ~ 'E'(f(B_17),f(suc(suc(B_17))))
    | ~ iLEQ(suc(A_4),suc(B_17))
    | ~ 'E'('0',f(suc(suc(B_17))))
    | ~ 'E'('0',f(B_17))
    | ~ 'E'('0',f(suc(suc(suc(B_17)))))
    | ~ 'E'('0',f(suc(A_4)))
    | ~ 'E'(f(B_17),f(suc(B_17)))
    | ~ 'E'('0',f(A_4))
    | 'E'(f(A_4),f(suc(A_4)))
    | 'E'(f(B_17),f(suc(suc(suc(B_17))))) ) ).

cnf(clause_265,axiom,
    ( ~ 'E'(s('0'),f(suc(B_14)))
    | ~ 'E'(s('0'),f(suc(suc(B_14))))
    | ~ 'E'(s('0'),f(suc(A_3)))
    | ~ 'E'(s('0'),f(B_14))
    | ~ 'E'(f(B_14),f(suc(B_14)))
    | ~ 'E'(s('0'),f(A_3))
    | ~ iLEQ(suc(A_3),suc(B_14))
    | 'E'(f(A_3),f(suc(A_3)))
    | 'E'(f(B_14),f(suc(suc(B_14)))) ) ).

cnf(clause_803,axiom,
    ( ~ 'E'(f(A_2),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(B_10))
    | ~ 'E'(s(s('0')),f(suc(A_2)))
    | ~ iLEQ(suc(A_2),suc(B_10))
    | ~ 'E'(s(s('0')),f(suc(B_10)))
    | ~ 'E'(s(s('0')),f(suc(suc(A_2))))
    | ~ 'E'(s(s('0')),f(A_2))
    | ~ 'E'(s(s('0')),f(suc(suc(suc(A_2)))))
    | ~ 'E'(f(A_2),f(suc(A_2)))
    | 'E'(f(A_2),f(suc(suc(suc(A_2)))))
    | 'E'(f(B_10),f(suc(B_10))) ) ).

cnf(clause_246,axiom,
    ( ~ 'LE'(f(suc(suc(B_16))),s('0'))
    | 'E'('0',f(suc(suc(B_16))))
    | 'LE'(f(B_16),'0') ) ).

cnf(clause_1086,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_5),f(suc(suc(B_5)))) ) ).

cnf(clause_254,axiom,
    ( ~ 'E'(s(s(s('0'))),f(suc(B_5)))
    | ~ 'E'(f(B_5),f(suc(B_5)))
    | ~ iLEQ(suc(A_1),suc(B_5))
    | ~ 'E'(s(s(s('0'))),f(B_5))
    | ~ 'E'(s(s(s('0'))),f(A_1))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(A_1))))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(suc(B_5)))))
    | ~ 'E'(f(A_1),f(suc(A_1)))
    | ~ 'E'(s(s(s('0'))),f(suc(suc(B_5))))
    | ~ 'E'(s(s(s('0'))),f(suc(A_1)))
    | ~ 'E'(f(B_5),f(suc(suc(B_5))))
    | 'E'(f(A_1),f(suc(suc(A_1))))
    | 'E'(f(B_5),f(suc(suc(suc(B_5))))) ) ).

%------------------------------------------------------------------------------
